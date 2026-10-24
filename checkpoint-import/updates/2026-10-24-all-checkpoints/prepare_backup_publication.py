#!/usr/bin/env python3
"""Prepare a verified backup-report release asset and a Git commit for publication.

The branch ref is deliberately left unchanged here; update it using the saved
expected parent SHA. Only the explicit allowlist below is published.
"""
from __future__ import annotations

import base64
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import zipfile

import upload_all_checkpoints as transfer

ROOT = Path(__file__).resolve().parent
PREFIX = 'checkpoint-import/updates/2026-10-24-all-checkpoints/'
REQUIRED = [
    'BACKUP_STATUS.md', 'ALL_CHECKPOINTS_STATE.json', 'ALL_CHECKPOINTS_SOURCE_INVENTORY.json',
    'ALL_CHECKPOINTS_ORIGINALS.csv', 'CHECKPOINT_COVERAGE.csv',
    'ALL_CHECKPOINTS_FINAL_REMOTE_AUDIT.json', 'ALL_CHECKPOINTS_BASELINE_ASSETS.json',
    'SOURCE_INVENTORY_REMOTE_RECEIPT.json', 'inventory_publication.log',
    'CHECKPOINT210_REMOTE_VERIFICATION.json', 'temporary_copy_cleanup.json',
    'STAGING_PARTIAL_CLEANUP.json',
    'legacy_coverage_93.json', 'legacy_coverage_115.json',
    'earlier_sources_through93.json', 'earlier_sources_through115.json',
    'upload_all_checkpoints.py', 'restore_original_checkpoint_files.py',
    'upload_all_checkpoints_v2.py', 'upload_all_checkpoints_v3.py', 'upload_all_checkpoints_v4.py',
    'TRANSFER_PROVENANCE.json',
    'finalize_backup_catalog.py', 'prepare_backup_publication.py',
    'test_upload_all_checkpoints.py', 'transfer_guard_tests_v4.log',
    'transfer_guard_tests_v5.log',
    'RESTORE_CHECKPOINT149_RECEIPT.json', 'RESTORE_CHECKPOINT152_RECEIPT.json',
    'RESTORE_CHECKPOINT210_RECEIPT.json', 'restore210_execution.log',
    'restore149_execution.log', 'restore152_execution.log', 'final_catalog_execution.log',
    'batch_run.log', 'all_upload_run.log', 'all_upload_run_v2.log',
    'all_upload_run_v3.log', 'all_upload_run_v4.log', 'all_upload_run_v5.log',
]


def post(endpoint, data, method='POST'):
    with tempfile.NamedTemporaryFile(mode='w', suffix='.json', dir='/tmp') as body:
        json.dump(data, body)
        body.flush()
        return transfer.api(endpoint, '--method', method, '--input', body.name)


def raw_readback(asset, original):
    with tempfile.TemporaryDirectory(prefix='checkpoint-report-readback-', dir='/tmp') as d:
        downloaded = Path(d) / original.name
        with downloaded.open('wb') as out:
            transfer.api(f"repos/{transfer.REPO}/releases/assets/{asset['id']}",
                         '-H', 'Accept: application/octet-stream', output=out)
        if downloaded.stat().st_size != original.stat().st_size or transfer.sha256(downloaded) != transfer.sha256(original):
            raise RuntimeError('Published catalog/report readback differs')
    return {'asset_id': asset['id'], 'name': asset['name'], 'size_bytes': asset['size'],
            'sha256': asset['digest'][7:], 'fresh_remote_download_matched': True,
            'browser_download_url': asset['browser_download_url']}


def run():
    state = json.loads((ROOT / 'ALL_CHECKPOINTS_STATE.json').read_text())
    audit = json.loads((ROOT / 'ALL_CHECKPOINTS_FINAL_REMOTE_AUDIT.json').read_text())
    if state['status'] != 'ALL_INVENTORIED_ORIGINAL_BYTES_BACKED_UP' or not audit['all_originals_have_remote_restore_locations']:
        raise RuntimeError('Cannot publish completion before successful transfer and audit')
    files = [ROOT / name for name in REQUIRED]
    files += sorted((ROOT / 'batch_receipts').glob('*.json'))
    if any(not p.is_file() for p in files):
        raise RuntimeError('A required evidence file is absent')
    # This explicit allowlist cannot include runtime/auth or raw Library list responses.
    catalog = ROOT / 'Paper_I_All_Checkpoints_20261024_Catalog.json'
    shutil.copyfile(ROOT / 'ALL_CHECKPOINTS_STATE.json', catalog)
    report = ROOT / 'Paper_I_All_Checkpoints_GitHub_Backup_Report_20261024.zip'
    manifest = {str(p.relative_to(ROOT)): {'size_bytes': p.stat().st_size, 'sha256': transfer.sha256(p)} for p in files}
    with zipfile.ZipFile(report, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        archive.writestr('REPORT_FILE_HASHES.json', json.dumps(manifest, indent=2) + '\n')
        for path in files:
            archive.write(path, str(path.relative_to(ROOT)))
    transfer.assert_private_target()
    published = []
    for path in (catalog, report):
        asset = transfer.upload_exact(path)
        published.append(raw_readback(asset, path))
    delivery = {'status': 'ALL_ORIGINALS_AND_REPORT_ASSETS_REMOTE_VERIFIED',
                'repository': transfer.REPO, 'release_id': transfer.RELEASE_ID,
                'checked_at': transfer.now(), 'files': published,
                'original_files': len(state['files']), 'original_bytes': audit['original_bytes'],
                'mathematical_verification': 'INCOMPLETE; no new Lean build or proof audit'}
    transfer.save(ROOT / 'FINAL_REPORT_ASSET_RECEIPT.json', delivery)
    files.append(ROOT / 'FINAL_REPORT_ASSET_RECEIPT.json')
    head = transfer.api(f'repos/{transfer.REPO}/git/ref/heads/main')['object']['sha']
    commit = transfer.api(f'repos/{transfer.REPO}/git/commits/{head}')
    tree_entries = []
    verified_blobs = []
    # Submit the text evidence as one tree operation. Its multi-megabyte request is
    # passed from disk to gh, avoiding tool-message truncation of the full catalog.
    for path in files:
        data = path.read_bytes()
        expected = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        relative = PREFIX + str(path.relative_to(ROOT))
        tree_entries.append({'path': relative, 'mode': '100644', 'type': 'blob', 'content': data.decode('utf-8')})
        verified_blobs.append({'path': relative, 'git_blob_sha': expected,
                               'sha256': hashlib.sha256(data).hexdigest(), 'size_bytes': len(data)})
    # Replace only this update directory's status README; earlier evidence remains intact.
    status = (ROOT / 'BACKUP_STATUS.md').read_text()
    tree_entries.append({'path': PREFIX + 'README.md', 'mode': '100644', 'type': 'blob', 'content': status})
    current_readme = transfer.api(f'repos/{transfer.REPO}/contents/README.md?ref={head}')
    original_readme = base64.b64decode(current_readme['content']).decode()
    banner = (f'> **2026-10-24 backup update:** All {len(state["files"]):,} inventoried checkpoint originals '
              f'are saved and verified. See the [complete backup report]({PREFIX}BACKUP_STATUS.md) '
              'and restore catalog. Historical checkpoints 72–75 remain unconfirmed.\n\n')
    tree_entries.append({'path': 'README.md', 'mode': '100644', 'type': 'blob', 'content': banner + original_readme})
    tree = post(f'repos/{transfer.REPO}/git/trees', {'base_tree': commit['tree']['sha'], 'tree': tree_entries})
    readback = transfer.api(f"repos/{transfer.REPO}/git/trees/{tree['sha']}?recursive=1")
    if readback.get('truncated'):
        raise RuntimeError('Remote tree readback is truncated')
    actual = {e['path']: e for e in readback['tree']}
    for entry in tree_entries:
        data = entry['content'].encode()
        expected = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        got = actual.get(entry['path'], {})
        if got.get('sha') != expected or got.get('size') != len(data) or got.get('type') != 'blob':
            raise RuntimeError('Remote Git tree bytes differ from a publication file')
    proposed = post(f'repos/{transfer.REPO}/git/commits',
                    {'message': 'Complete backup of all 1,087 inventoried Lean checkpoint originals with restore catalog and verification evidence',
                     'tree': tree['sha'], 'parents': [head]})
    result = {'status': 'PREPARED_VERIFIED_PUBLICATION_COMMIT', 'repository': transfer.REPO,
              'expected_parent_sha': head, 'commit_sha': proposed['sha'], 'tree_sha': tree['sha'],
              'file_count': len(tree_entries), 'verified_blobs': verified_blobs,
              'ref_updated_by_this_script': False, 'created_at': transfer.now()}
    transfer.save(ROOT / 'PUBLICATION_CANDIDATE.json', result)
    print(json.dumps({k: v for k, v in result.items() if k != 'verified_blobs'}), flush=True)


if __name__ == '__main__':
    run()
