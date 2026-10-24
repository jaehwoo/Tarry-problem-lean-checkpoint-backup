import io
import unittest
from email.message import Message
from unittest import mock
import urllib.error

import strict_github_transport as transport


class StrictDestinationTests(unittest.TestCase):
    def test_unexpected_host_rejected_before_credential_or_network(self):
        with mock.patch.object(transport, 'credential') as credential:
            with mock.patch.object(transport.urllib.request, 'build_opener') as opener:
                for url in ('https://cafe.github.com/upload',
                            'https://uploads.github.com.attacker.invalid/a',
                            'http://api.github.com/user',
                            'https://api.github.com@attacker.invalid/user'):
                    with self.assertRaises(transport.DestinationRejected):
                        transport.api(url)
                credential.assert_not_called()
                opener.assert_not_called()

    def test_upload_redirect_not_replayed(self):
        url = f'https://uploads.github.com/repos/{transport.REPO}/releases/{transport.RELEASE_ID}/assets?name=test'
        headers = Message()
        headers['Location'] = 'https://cafe.github.com/upload'
        opener = mock.Mock()
        opener.open.side_effect = urllib.error.HTTPError(url, 307, 'redirect', headers, io.BytesIO())
        with mock.patch.object(transport.urllib.request, 'build_opener', return_value=opener), mock.patch.object(transport, 'audit'):
            with self.assertRaises(transport.DestinationRejected):
                transport.request(url, 'POST', {}, io.BytesIO(b'test'), None, 'synthetic-token', 2)
        self.assertEqual(opener.open.call_count, 1)

    def test_unexpected_download_redirect_is_not_followed(self):
        url = f'https://api.github.com/repos/{transport.REPO}/releases/assets/1'
        headers = Message()
        headers['Location'] = 'https://cafe.github.com/download'
        opener = mock.Mock()
        opener.open.side_effect = urllib.error.HTTPError(url, 302, 'redirect', headers, io.BytesIO())
        with mock.patch.object(transport.urllib.request, 'build_opener', return_value=opener), mock.patch.object(transport, 'audit'):
            with self.assertRaises(transport.DestinationRejected):
                transport.request(url, 'GET', {}, None, io.BytesIO(), 'synthetic-token', 2)
        self.assertEqual(opener.open.call_count, 1)

    def test_approved_download_has_no_authentication(self):
        url = f'https://api.github.com/repos/{transport.REPO}/releases/assets/1'
        headers = Message()
        headers['Location'] = f'https://release-assets.githubusercontent.com/github-production-release-asset/{transport.REPO_ID}/test?redacted=test'
        response = io.BytesIO(b'restored')
        response.status = 200
        response.headers = Message()
        opener = mock.Mock()
        opener.open.side_effect = [urllib.error.HTTPError(url, 302, 'redirect', headers, io.BytesIO()), response]
        output = io.BytesIO()
        with mock.patch.object(transport.urllib.request, 'build_opener', return_value=opener), mock.patch.object(transport, 'audit'):
            transport.request(url, 'GET', {}, None, output, 'synthetic-token', 2)
        first, second = [c.args[0] for c in opener.open.call_args_list]
        self.assertEqual(first.get_header('Authorization'), 'Bearer synthetic-token')
        self.assertFalse(second.has_header('Authorization'))
        self.assertIsNone(second.data)
        self.assertEqual(output.getvalue(), b'restored')

    def test_only_same_repository_numeric_pagination_allowed(self):
        value = transport.normalize_pagination(f'https://api.github.com/repositories/{transport.REPO_ID}/releases/422682291/assets?page=2')
        self.assertEqual(value, f'https://api.github.com/repos/{transport.REPO}/releases/422682291/assets?page=2')
        for invalid in ('https://cafe.github.com/repositories/1417233863/releases',
                        'https://api.github.com/repositories/1/releases'):
            with self.assertRaises(transport.DestinationRejected):
                transport.normalize_pagination(invalid)

    def test_other_repository_and_write_scope_refused(self):
        for url, method in [('https://api.github.com/repos/other/repo', 'GET'),
                            (f'https://api.github.com/repos/{transport.REPO}', 'DELETE'),
                            (f'https://api.github.com/repos/{transport.REPO}/issues', 'POST')]:
            with self.assertRaises(transport.DestinationRejected):
                transport.validated_url(url, method)


if __name__ == '__main__':
    unittest.main()
