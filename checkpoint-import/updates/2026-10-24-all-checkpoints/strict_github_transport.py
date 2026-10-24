#!/usr/bin/env python3
"""GitHub backup transport with an explicit destination and redirect policy.

Uses the already-authorized GitHub CLI only to obtain its github.com credential
in memory. Tokens, response bodies and signed download queries are never logged.
The standard TLS verification and environment proxy configuration are retained.
No request to cafe.github.com, or to any other unlisted host, is permitted.
"""
from __future__ import annotations

import datetime as dt
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
import urllib.error
import urllib.parse
import urllib.request

ROOT = Path(__file__).resolve().parent
REPO = 'jaehwoo/lean-checkpoint-backup'
REPO_ID = 1417233863
RELEASE_ID = 422682291
AUDIT = ROOT / 'STRICT_ENDPOINT_AUDIT.jsonl'


class DestinationRejected(RuntimeError):
    pass


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def validated_url(url, method, *, download=False):
    p = urllib.parse.urlsplit(url)
    if (p.scheme != 'https' or p.username or p.password or p.port not in (None, 443)
            or p.fragment or '%' in p.netloc or '\\' in url):
        raise DestinationRejected('Only ordinary HTTPS destinations are permitted')
    if p.hostname == 'api.github.com':
        base = f'/repos/{REPO}'
        allowed = p.path == '/user' or p.path == base or p.path.startswith(base + '/')
        if not allowed or '..' in p.path or '%' in p.path:
            raise DestinationRejected('API request is outside the designated repository')
        if method == 'GET':
            return p
        if method == 'POST' and p.path in (base + '/git/trees', base + '/git/commits'):
            return p
        if method == 'PATCH' and p.path == base + f'/releases/{RELEASE_ID}':
            return p
        raise DestinationRejected('API mutation is outside the backup publication scope')
    if (p.hostname == 'uploads.github.com' and method == 'POST' and
            p.path == f'/repos/{REPO}/releases/{RELEASE_ID}/assets'):
        return p
    if (download and method == 'GET' and p.hostname == 'release-assets.githubusercontent.com'
            and p.path.startswith(f'/github-production-release-asset/{REPO_ID}/')):
        return p
    raise DestinationRejected('Unexpected destination host; request stopped before transmission')


def credential(gh, auth_dir):
    env = os.environ.copy()
    env.pop('GH_DEBUG', None)
    if auth_dir is not None:
        env['GH_CONFIG_DIR'] = str(auth_dir)
    env['GH_PROMPT_DISABLED'] = '1'
    result = subprocess.run([str(gh), 'auth', 'token', '--hostname', 'github.com'],
                            env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            timeout=20)
    if result.returncode or not result.stdout.strip():
        raise RuntimeError('The already-authorized github.com CLI credential is unavailable')
    return result.stdout.decode().strip()


def audit(method, url, authenticated, status):
    p = urllib.parse.urlsplit(url)
    with AUDIT.open('a') as out:
        out.write(json.dumps({'at': dt.datetime.now(dt.timezone.utc).isoformat(),
                              'method': method, 'host': p.hostname, 'path': p.path,
                              'authenticated': authenticated, 'status': status}) + '\n')


def request(url, method, headers, body, output, token, timeout):
    parsed = validated_url(url, method)
    is_download = (method == 'GET' and output is not None and
                   re.fullmatch(f'/repos/{REPO}/releases/assets/[0-9]+', parsed.path))
    opener = urllib.request.build_opener(NoRedirect())
    for hop in range(2):
        parsed = validated_url(url, method, download=bool(hop and is_download))
        authenticated = parsed.hostname in ('api.github.com', 'uploads.github.com')
        request_headers = {'User-Agent': 'Paper-I-private-checkpoint-backup/strict-v1',
                           'Accept': 'application/vnd.github+json', **headers}
        if any(k.lower() in ('authorization', 'host', 'proxy-authorization') for k in headers):
            raise DestinationRejected('Caller cannot override credentials or destination headers')
        if authenticated:
            request_headers['Authorization'] = 'Bearer ' + token
            request_headers['X-GitHub-Api-Version'] = '2022-11-28'
        req = urllib.request.Request(url, data=body, method=method, headers=request_headers)
        try:
            response = opener.open(req, timeout=timeout)
        except urllib.error.HTTPError as error:
            audit(method, url, authenticated, error.code)
            if error.code in (301, 302, 303, 307, 308):
                location = error.headers.get('Location', '')
                error.close()
                if not (is_download and hop == 0 and method == 'GET' and body is None):
                    raise DestinationRejected('Redirect refused; no upload or API mutation replayed') from None
                # Validate BEFORE constructing the follow-up request, without passing
                # GitHub authentication to the download CDN.
                target = urllib.parse.urljoin(url, location)
                p = validated_url(target, 'GET', download=True)
                if p.hostname != 'release-assets.githubusercontent.com':
                    raise DestinationRejected('Asset redirect is not the approved GitHub CDN')
                url = target
                continue
            error.close()
            raise RuntimeError(f'GitHub HTTP {error.code} at approved host {parsed.hostname}') from None
        except (urllib.error.URLError, TimeoutError, OSError):
            audit(method, url, authenticated, 'connection_failed')
            raise RuntimeError(f'GitHub connection failed at approved host {parsed.hostname}') from None
        with response:
            audit(method, url, authenticated, response.status)
            response_headers = response.headers
            if output is not None:
                shutil.copyfileobj(response, output, length=4 * 1024 * 1024)
                return None, response_headers
            raw = response.read()
            return json.loads(raw) if raw.strip() else None, response_headers
    raise DestinationRejected('Too many redirects')


def normalize_pagination(url):
    # GitHub's observed Link header uses the same repository's numeric-ID route.
    # Normalize only that exact ID back to the already-approved owner/name route.
    p = urllib.parse.urlsplit(url)
    prefix = f'/repositories/{REPO_ID}/'
    if p.path.startswith(prefix):
        p = p._replace(path=f'/repos/{REPO}/' + p.path[len(prefix):])
    normalized = p.geturl()
    validated_url(normalized, 'GET')
    return normalized


def api(endpoint, *args, output=None, timeout=1800, gh=None, auth_dir=None):
    method, headers, input_file, paginate, slurp = 'GET', {}, None, False, False
    args = iter(args)
    for option in args:
        if option in ('--method', '-X'):
            method = next(args).upper()
        elif option in ('--header', '-H'):
            key, value = next(args).split(':', 1)
            headers[key.strip()] = value.strip()
        elif option == '--input':
            input_file = Path(next(args))
        elif option == '--paginate':
            paginate = True
        elif option == '--slurp':
            slurp = True
        else:
            raise RuntimeError('Unsupported API option in strict backup transport')
    url = endpoint if '://' in endpoint else 'https://api.github.com/' + endpoint.lstrip('/')
    validated_url(url, method)
    if input_file is not None and method == 'GET':
        raise DestinationRejected('GET requests cannot include checkpoint payloads')
    gh = gh or ROOT / 'runtime/gh'
    if auth_dir is None and (ROOT / 'runtime/auth').is_dir():
        auth_dir = ROOT / 'runtime/auth'
    token = credential(gh, auth_dir)
    pages = []
    while url:
        validated_url(url, method)
        for attempt in range(4):
            if attempt and output is not None:
                output.seek(0)
                output.truncate()
            try:
                if input_file is None:
                    result, response_headers = request(url, method, headers, None, output, token, timeout)
                else:
                    with input_file.open('rb') as body:
                        sent_headers = {'Content-Type': 'application/json',
                                        'Content-Length': str(input_file.stat().st_size), **headers}
                        result, response_headers = request(url, method, sent_headers, body, output, token, timeout)
                break
            except DestinationRejected:
                raise
            except RuntimeError as error:
                transient = any(s in str(error) for s in ('connection failed', 'HTTP 502', 'HTTP 503', 'HTTP 504'))
                if not (method == 'GET' and transient and attempt < 3):
                    raise
                time.sleep(2 ** (attempt + 1))
        if output is not None:
            return None
        pages.append(result)
        next_url = None
        if paginate:
            for link in response_headers.get('Link', '').split(','):
                if 'rel="next"' in link:
                    match = re.search(r'<([^>]+)>', link)
                    if not match:
                        raise DestinationRejected('Malformed pagination link')
                    next_url = normalize_pagination(match.group(1))
                    old, new = urllib.parse.urlsplit(url), validated_url(next_url, 'GET')
                    if new.hostname != old.hostname or new.path != old.path:
                        raise DestinationRejected('Pagination attempted to change destination')
        url = next_url
    return pages if slurp else pages[0]
