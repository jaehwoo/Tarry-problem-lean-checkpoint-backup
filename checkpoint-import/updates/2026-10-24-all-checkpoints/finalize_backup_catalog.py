#!/usr/bin/env python3
"""Audit the completed remote backup and produce its reviewable restore catalog.

This audits backup bytes and metadata only. It never edits or compiles Lean.
"""
from __future__ import annotations

import csv
from collections import Counter
import datetime as dt
import hashlib
import json
from pathlib import Path
from zoneinfo import ZoneInfo

import upload_all_checkpoints as transfer

ROOT = Path(__file__).resolve().parent


def run():
    state = json.loads((ROOT / 'ALL_CHECKPOINTS_STATE.json').read_text())
    queue = json.loads((ROOT / 'upload_queue.json').read_text())['entries']
    if state['status'] != 'ALL_INVENTORIED_ORIGINAL_BYTES_BACKED_UP':
        raise RuntimeError('Transfer is incomplete; no completed-backup report generated')
    by_id = {e['library_file_id']: e for e in queue}
    if len(by_id) != len(queue) or set(by_id) != set(state['files']):
        raise RuntimeError('Original inventory and completed ledger differ')
    paths = [e['path'] for e in queue]
    if len(paths) != len(set(paths)):
        raise RuntimeError('Original restore paths conflict')
    transfer.assert_private_target()
    releases, assets = transfer.releases_and_assets()
    by_asset = {a['id']: a for a in assets}
    baseline = json.loads((ROOT / 'ALL_CHECKPOINTS_BASELINE_ASSETS.json').read_text())
    if any(transfer.clean_asset(by_asset.get(a['id'], {})) != a for a in baseline):
        raise RuntimeError('A preexisting release asset changed')
    receipt_ids = []
    receipt_details = []
    for batch in state['batches']:
        path = ROOT / 'batch_receipts' / batch['receipt_asset']['name']
        receipt = json.loads(path.read_text())
        digest = transfer.sha256(path)
        asset = by_asset[batch['receipt_asset']['id']]
        if asset['state'] != 'uploaded' or asset['size'] != path.stat().st_size or asset['digest'] != 'sha256:' + digest:
            raise RuntimeError('A remote batch receipt differs from the saved local receipt')
        receipt_details.append({'batch': batch['batch'], 'asset_id': asset['id'],
                                'sha256': digest, 'source_files': len(receipt['files'])})
        for record in receipt['files']:
            receipt_ids.append(record['library_file_id'])
            if state['files'][record['library_file_id']] != record:
                raise RuntimeError('Per-batch receipt and completed ledger differ')
    if Counter(receipt_ids) != Counter(by_id.keys()):
        raise RuntimeError('Batch receipts do not cover the inventory exactly once')
    rows = []
    for key, entry in by_id.items():
        record = state['files'][key]
        if (record['library_path'] != entry['path'] or record['original_name'] != entry['name']
                or record['size_bytes'] != entry['size_bytes']):
            raise RuntimeError('Original identity or size differs from inventory')
        if len(record['sha256']) != 64 or any(c not in '0123456789abcdef' for c in record['sha256']):
            raise RuntimeError('Invalid original SHA-256')
        location = record['restore_from']
        asset = by_asset[location['asset_id']]
        if (asset['state'] != 'uploaded' or asset['digest'] != 'sha256:' + location['asset_sha256']
                or asset['name'] != location['asset'] or asset['release_id'] != location['release_id']):
            raise RuntimeError('A catalog restore asset is missing or changed')
        if location['member'] is None and (asset['size'] != record['size_bytes']
                                           or location['asset_sha256'] != record['sha256']):
            raise RuntimeError('Direct restore asset is not the original bytes')
        rows.append({'checkpoint': record['checkpoint'], 'library_file_id': key,
                     'original_path': record['library_path'], 'size_bytes': record['size_bytes'],
                     'sha256': record['sha256'], 'verification_status': record['status'],
                     **{k: location[k] for k in ('release_id', 'asset_id', 'asset', 'asset_sha256', 'member')}})
    rows.sort(key=lambda r: (r['checkpoint'] is None, r['checkpoint'] or 0, r['original_path']))
    with (ROOT / 'ALL_CHECKPOINTS_ORIGINALS.csv').open('w', newline='') as out:
        writer = csv.DictWriter(out, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    public_inventory = {'scope': 'All available checkpoint originals in the saved root and /Tarry inventory',
                        'file_count': len(queue), 'total_original_bytes': sum(e['size_bytes'] for e in queue),
                        'entries': [{k: e.get(k) for k in ('library_file_id', 'version_id', 'path', 'name',
                                    'checkpoint', 'size_bytes', 'created_at', 'modified_at')} for e in queue]}
    transfer.save(ROOT / 'ALL_CHECKPOINTS_SOURCE_INVENTORY.json', public_inventory)
    coverage = []
    old93 = json.loads((ROOT / 'legacy_coverage_93.json').read_text())
    old115 = json.loads((ROOT / 'legacy_coverage_115.json').read_text())
    for number in range(1, 211):
        files = [r for r in rows if r['checkpoint'] == number]
        prior = 'earlier verified archive' if str(number) in old93['checkpoint_archives'] else ''
        if number in old115['complete_project_numbers']:
            prior = 'earlier catalog: completed checkpoint package'
        if number == 109:
            prior = 'earlier catalog: progress-only, not a completed checkpoint package'
        if number in (72, 73, 74, 75):
            prior = 'unconfirmed in available historical records'
        if number == 1:
            prior += '; initial Pilot convention'
        coverage.append({'checkpoint': number, 'inventoried_original_files': len(files),
                         'inventoried_original_bytes': sum(r['size_bytes'] for r in files),
                         'all_inventoried_originals_backed_up': bool(files),
                         'historical_catalog_status': prior,
                         'mathematical_verification': 'Not assessed by this backup operation'})
    with (ROOT / 'CHECKPOINT_COVERAGE.csv').open('w', newline='') as out:
        writer = csv.DictWriter(out, fieldnames=list(coverage[0]))
        writer.writeheader()
        writer.writerows(coverage)
    checked_at = dt.datetime.now(dt.timezone.utc)
    new_assets = [b['asset'] for b in state['batches'] if b['asset']]
    counts = Counter(r['verification_status'] for r in rows)
    restore_tests = []
    for number in (149, 152, 210):
        name = f'RESTORE_CHECKPOINT{number}_RECEIPT.json'
        receipt = json.loads((ROOT / name).read_text())
        expected_ids = {r['library_file_id'] for r in rows if r['checkpoint'] == number}
        if receipt['status'] != 'ORIGINAL_ARTIFACT_RESTORE_VERIFIED' or {f['library_file_id'] for f in receipt['files']} != expected_ids:
            raise RuntimeError('A restore test does not cover its checkpoint originals')
        for restored in receipt['files']:
            source = state['files'][restored['library_file_id']]
            if (not restored['disk_readback_matched'] or restored['sha256'] != source['sha256']
                    or restored['size_bytes'] != source['size_bytes']):
                raise RuntimeError('A restore-test file differs from the final catalog')
        restore_tests.append(name)
    versions = {transfer.sha256(p): p.name for p in ROOT.glob('upload_all_checkpoints*.py')}
    if any(h not in versions for h in state.get('uploader_versions', [])):
        raise RuntimeError('A recorded uploader source version has not been preserved')
    provenance = {'recorded_versions': {h: versions[h] for h in state.get('uploader_versions', [])},
                  'batches': [{'batch': b['batch'], 'uploader_sha256': b.get('uploader_sha256'),
                              'source_file': versions.get(b.get('uploader_sha256'))} for b in state['batches']],
                  'earlier_tooling_commit': '1fe78d66e7dcb75f5d14d0fd37d718411aa50c96',
                  'note': 'Early receipts without an uploader hash are identified explicitly; their remote-byte checks remain recorded in the transfer logs and receipts. The v2 source was reconstructed and matched exactly to its previously recorded SHA-256.'}
    transfer.save(ROOT / 'TRANSFER_PROVENANCE.json', provenance)
    audit = {'status': 'ALL_INVENTORIED_ORIGINAL_BYTES_BACKED_UP_AND_REMOTE_CATALOG_AUDITED',
             'checked_at_utc': checked_at.isoformat(),
             'checked_at_seoul': checked_at.astimezone(ZoneInfo('Asia/Seoul')).isoformat(),
             'repository': transfer.REPO, 'repository_id': transfer.REPO_ID, 'private': True,
             'inventory_files': len(queue), 'original_bytes': sum(r['size_bytes'] for r in rows),
             'original_unique_sha256': len({r['sha256'] for r in rows}), 'verification_counts': dict(counts),
             'batches': len(state['batches']), 'new_data_assets': len(new_assets),
             'new_data_asset_bytes': sum(a['size'] for a in new_assets),
             'all_originals_have_remote_restore_locations': True,
             'all_batch_receipts_match_saved_ledger': True,
             'all_recorded_uploader_versions_preserved': True,
             'all_preexisting_assets_unchanged': True, 'preexisting_asset_count': len(baseline),
             'new_data_verification': 'Fresh GitHub download; SHA-256 of entire container and every original payload',
             'reused_data_verification': 'Original source SHA-256 matched a preserved asset or prior verified archive catalog; remote asset digest rechecked',
             'restore_tests': restore_tests,
             'historical_unconfirmed_checkpoints': [72, 73, 74, 75],
             'historical_progress_only_checkpoint': 109,
             'manuscript_and_lean_edited': False, 'lean_build_performed': False,
             'manuscript_verification': 'INCOMPLETE; backup verification is not mathematical verification',
             'receipt_assets': receipt_details,
             'release_assets': [transfer.clean_asset(a) for a in assets]}
    transfer.save(ROOT / 'ALL_CHECKPOINTS_FINAL_REMOTE_AUDIT.json', audit)
    total = audit['original_bytes']
    text = f'''# All available Lean checkpoint originals: GitHub backup

Status: **all {len(queue):,} inventoried original files backed up and the remote catalog audited**.
Checked: {audit['checked_at_seoul']} (Asia/Seoul).
Repository: https://github.com/{transfer.REPO} (private).

The inventory accounts for **{total:,} bytes** before deduplication and backup compression.
There are {len(state['batches'])} saved batch receipts and {len(new_assets)} newly uploaded data containers.
The {len(baseline)} assets present before this continuation remain unchanged. Original filenames,
paths, sizes and SHA-256 hashes are listed in `ALL_CHECKPOINTS_ORIGINALS.csv`.
The complete machine-readable restore map is `ALL_CHECKPOINTS_STATE.json`.

## What was checked

Every original source was SHA-256 hashed. For every new data container, the complete uploaded
container was downloaded from GitHub again, its hash checked, and every original member's
size and hash checked. Identical bytes already in a preserved GitHub asset or an earlier
verified archive were reused by hash; their remote container digest was rechecked.
The final audit checks that each inventory file occurs in exactly one batch receipt, all
receipts agree with the completed ledger, and every restore location points to an intact
remote asset. Credentials and runtime authentication files are excluded from this backup.

Actual fresh restore tests passed for checkpoints 149 (ZIP container), 152
(tar.zst container), and the latest checkpoint 210, including a second hash read from the restored disk files. Their
receipts and executed command logs are saved beside this report. The seven synthetic transfer
guard tests passed; these tests supplement the actual transfer evidence and do not replace it.

## Historical scope and limitations

Earlier verified archives preserve checkpoints 1–71 and 76–93; checkpoint 1 uses the
initial Pilot convention. The earlier through-115 catalog records completed packages
for 94–108 and 110–115, and progress-only material for 109. Checkpoints **72–75 remain
unconfirmed** in the available history. Current named originals extend through checkpoint
210 and include progress/recovery packages, reports, checklists, correspondence, build
evidence and environment recovery files. A backed-up original is not necessarily a standalone
complete Lean environment. `CHECKPOINT_COVERAGE.csv` distinguishes inventory counts from
the historical catalog classifications. Refer to the original checkpoint instructions for
incremental project reconstruction.

**The manuscript and Lean source were not modified. No new Lean build or mathematical proof
verification was performed for this backup. Manuscript verification remains incomplete.**
Earlier proof-status claims and limitations are preserved as originally recorded.

## Restore original artifacts

Install Python with the `zstandard` package and authenticate GitHub CLI to this private
repository. Run, for example:

```sh
python3 restore_original_checkpoint_files.py \\
  --catalog ALL_CHECKPOINTS_STATE.json --checkpoint 210 \\
  --assets downloaded-assets --destination restored-checkpoint-210 --download
```

Use `--all` instead of `--checkpoint 210` to restore the entire inventoried original-file set.
The destination must not already exist. Allow enough disk space for both downloaded backup
containers and the {total:,} original bytes. The restore tool validates hashes, refuses to
overwrite files, and writes a restore receipt. It restores the original archives and companion
files; follow their own instructions to assemble the pinned Lean project.

Catalog and audit files: `ALL_CHECKPOINTS_STATE.json`, `ALL_CHECKPOINTS_SOURCE_INVENTORY.json`,
`ALL_CHECKPOINTS_ORIGINALS.csv`, `CHECKPOINT_COVERAGE.csv`, `ALL_CHECKPOINTS_FINAL_REMOTE_AUDIT.json`.
'''
    (ROOT / 'BACKUP_STATUS.md').write_text(text)
    print(json.dumps({k: v for k, v in audit.items() if k not in ('receipt_assets', 'release_assets')}))


if __name__ == '__main__':
    run()
