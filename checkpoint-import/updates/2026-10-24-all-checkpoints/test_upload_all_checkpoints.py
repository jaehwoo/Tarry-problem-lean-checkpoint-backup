"""Synthetic integrity/overwrite guards, not evidence of a real remote backup."""
import contextlib
import hashlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import upload_all_checkpoints as backup


class TransferIntegrityTests(unittest.TestCase):
    def test_conflicting_remote_asset_is_never_overwritten(self):
        with tempfile.TemporaryDirectory() as tmp:
            f = Path(tmp) / 'sample.bin'
            f.write_bytes(b'original')
            remote = {'name': f.name, 'state': 'uploaded', 'size': 8, 'digest': 'sha256:' + '0' * 64}
            with patch.object(backup, 'assert_private_target'), patch.object(
                    backup, 'current_release_assets', return_value=[remote]), patch.object(backup, 'api') as call:
                with self.assertRaisesRegex(RuntimeError, 'conflicts'):
                    backup.upload_exact(f)
                call.assert_not_called()

    def test_remote_corruption_fails_and_partial_download_is_removed(self):
        with tempfile.TemporaryDirectory() as tmp:
            f = Path(tmp) / 'sample.bin'
            f.write_bytes(b'original')
            def corrupt(*args, **kw):
                kw['output'].write(b'corrupt!')
            with patch.object(backup, 'PARTS', Path(tmp)), patch.object(backup, 'api', side_effect=corrupt):
                with self.assertRaisesRegex(RuntimeError, 'differ'):
                    backup.fresh_download_verify({'id': 1}, f)
            self.assertFalse((Path(tmp) / 'sample.bin.remote-download').exists())

    def test_staging_path_cannot_escape(self):
        with self.assertRaisesRegex(RuntimeError, 'escapes'):
            backup.source_path({'path': '../../outside'})

    def test_remote_zip_payload_checked_against_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / 'original.bin'
            source.write_bytes(b'checkpoint bytes\x00\xff')
            h = hashlib.sha256(source.read_bytes()).hexdigest()
            payload = {'member': 'originals/id/original.bin', 'original_name': 'original.bin',
                       'library_path': '/original.bin', 'library_file_id': 'id',
                       'size_bytes': source.stat().st_size, 'sha256': h, 'local_path': str(source)}
            with patch.object(backup, 'PARTS', root):
                part = backup.build_part([payload], 1)
                def download(*args, **kw):
                    kw['output'].write(part.read_bytes())
                with patch.object(backup, 'api', side_effect=download), contextlib.redirect_stdout(io.StringIO()):
                    backup.fresh_download_verify({'id': 1}, part)

    def test_receipt_with_missing_or_changed_remote_anchor_cannot_resume(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            receipt = {'files': [{'library_file_id': 'id', 'restore_from': {
                'asset_id': 1, 'asset_sha256': 'a' * 64}}]}
            (root / 'Paper_I_All_Checkpoints_20261024_Batch_001_Receipt.json').write_text(json.dumps(receipt))
            with patch.object(backup, 'RECEIPTS', root), patch.object(backup, 'api', return_value={
                    'state': 'uploaded', 'digest': 'sha256:' + 'b' * 64}), patch.object(backup, 'upload_exact') as upload:
                with self.assertRaisesRegex(RuntimeError, 'not intact'):
                    backup.resume_receipt({'files': {}, 'batches': []}, [{'library_file_id': 'id'}], 1)
                upload.assert_not_called()


if __name__ == '__main__':
    unittest.main()
