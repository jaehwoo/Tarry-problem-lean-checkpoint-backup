#!/usr/bin/env python3
"""Resumable private Release backup of unchanged checkpoint originals.

No manuscript or Lean source is edited. Library downloads use the current
official helper. A newly uploaded part is downloaded again and checked before
its staged source copies are removed. Credentials remain in gh's auth store;
this program neither reads nor prints authentication values.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import time
import urllib.parse
import zipfile
import zstandard

ROOT = Path(__file__).resolve().parent
WORKSPACE = ROOT.parent
REPO = 'jaehwoo/lean-checkpoint-backup'
REPO_ID = 1417233863
RELEASE_ID = 422682291
GH = ROOT / 'runtime/gh'
AUTH_DIR = ROOT / 'runtime/auth'
STATE = ROOT / 'ALL_CHECKPOINTS_STATE.json'
STAGE = ROOT / 'staging'
PARTS = Path('/tmp/paper_i_checkpoint_upload_9e45cd855c91')
RECEIPTS = ROOT / 'batch_receipts'
UPLOAD_CONTEXT = None
SCRIPT_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def now():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def emit(event, **data):
    print(json.dumps({'at': now(), 'event': event, **data}), flush=True)


def save(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + '.pending')
    with tmp.open('w') as out:
        json.dump(obj, out, indent=2, ensure_ascii=False)
        out.write('\n')
        out.flush()
        os.fsync(out.fileno())
    os.replace(tmp, path)


def sha256(path):
    with path.open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def gh(args, *, output=None, timeout=1800):
    env = os.environ.copy()
    env['GH_CONFIG_DIR'] = str(AUTH_DIR)
    env['GH_PROMPT_DISABLED'] = '1'
    env.pop('GH_DEBUG', None)
    result = subprocess.run([str(GH), *args], stdout=output or subprocess.PIPE,
                            stderr=subprocess.PIPE, env=env, timeout=timeout)
    if result.returncode:
        message = result.stderr.decode('utf-8', 'replace')[-2000:]
        raise RuntimeError(f'gh failed ({result.returncode}): {message}')
    if output is not None:
        return None
    return json.loads(result.stdout) if result.stdout.strip() else None


def api(endpoint, *args, **kw):
    return gh(['api', endpoint, *args], **kw)


def assert_private_target():
    repo = api(f'repos/{REPO}')
    if repo['id'] != REPO_ID or not repo['private'] or repo['full_name'] != REPO:
        raise RuntimeError('Repository identity or private visibility changed')
    if not repo.get('permissions', {}).get('push'):
        raise RuntimeError('No write permission for the designated backup repository')


def releases_and_assets():
    pages = api(f'repos/{REPO}/releases?per_page=100', '--paginate', '--slurp')
    releases = [r for page in pages for r in page]
    assets = []
    for release in releases:
        pages = api(f"repos/{REPO}/releases/{release['id']}/assets?per_page=100",
                    '--paginate', '--slurp')
        for page in pages:
            for a in page:
                assets.append({**a, 'release_id': release['id']})
    return releases, assets


def clean_asset(a):
    return {k: a.get(k) for k in ('id', 'name', 'size', 'state', 'digest', 'release_id')}


def current_release_assets():
    pages = api(f'repos/{REPO}/releases/{RELEASE_ID}/assets?per_page=100',
                '--paginate', '--slurp')
    return [a for page in pages for a in page]


def upload_exact(path):
    if UPLOAD_CONTEXT is None:
        assert_private_target()
    digest = sha256(path)
    size = path.stat().st_size
    assets = UPLOAD_CONTEXT['assets'] if UPLOAD_CONTEXT is not None else current_release_assets()
    previous = next((a for a in assets if a['name'] == path.name), None)
    if previous is None:
        release = UPLOAD_CONTEXT['release'] if UPLOAD_CONTEXT is not None else api(f'repos/{REPO}/releases/{RELEASE_ID}')
        if not release['draft']:
            raise RuntimeError('Expected the existing draft backup release')
        endpoint = release['upload_url'].split('{', 1)[0]
        expected = f'https://uploads.github.com/repos/{REPO}/releases/{RELEASE_ID}/assets'
        if endpoint != expected:
            raise RuntimeError('Unexpected upload destination')
        endpoint += '?' + urllib.parse.urlencode({'name': path.name})
        emit('upload_start', file=path.name, bytes=size)
        try:
            previous = api(endpoint, '--method', 'POST', '--input', str(path),
                           '-H', 'Content-Type: application/octet-stream')
        except (RuntimeError, subprocess.TimeoutExpired):
            previous = next((a for a in current_release_assets() if a['name'] == path.name), None)
            if previous is None:
                raise
    if (previous['state'] != 'uploaded' or previous['size'] != size
            or previous.get('digest') != 'sha256:' + digest):
        raise RuntimeError(f'Existing/uploaded asset conflicts with {path.name}; no overwrite attempted')
    previous['release_id'] = RELEASE_ID
    if UPLOAD_CONTEXT is not None and not any(a['id'] == previous['id'] for a in assets):
        assets.append(previous)
    emit('asset_digest_verified', file=path.name, asset_id=previous['id'], sha256=digest)
    return previous


def fresh_download_verify(asset, expected_path):
    restored = PARTS / (expected_path.name + '.remote-download')
    try:
        with restored.open('wb') as out:
            api(f"repos/{REPO}/releases/assets/{asset['id']}",
                '-H', 'Accept: application/octet-stream', output=out)
        digest = sha256(restored)
        if restored.stat().st_size != expected_path.stat().st_size or digest != sha256(expected_path):
            raise RuntimeError(f'Remote download bytes differ: {expected_path.name}')
        if expected_path.suffix == '.zip':
            with zipfile.ZipFile(restored) as archive:
                manifest = json.loads(archive.read('BACKUP_MANIFEST.json'))
                actual_names = set(archive.namelist())
                expected_names = {'BACKUP_MANIFEST.json'} | {f['member'] for f in manifest['payloads']}
                if actual_names != expected_names:
                    raise RuntimeError('Remote ZIP member inventory differs')
                for f in manifest['payloads']:
                    with archive.open(f['member']) as source:
                        h = hashlib.file_digest(source, 'sha256').hexdigest()
                    if h != f['sha256'] or archive.getinfo(f['member']).file_size != f['size_bytes']:
                        raise RuntimeError('Remote ZIP payload hash differs')
        elif expected_path.name.endswith('.tar.zst'):
            with restored.open('rb') as raw:
                header = raw.read(18)
            if zstandard.get_frame_parameters(header).window_size > (1 << 30):
                raise RuntimeError('Backup compression window exceeds the supported 1 GiB')
            with restored.open('rb') as raw, zstandard.ZstdDecompressor(max_window_size=1 << 30).stream_reader(raw) as reader:
                with tarfile.open(mode='r|', fileobj=reader) as archive:
                    first = next(iter(archive))
                    if first.name != 'BACKUP_MANIFEST.json' or not first.isfile():
                        raise RuntimeError('Remote tar manifest is absent')
                    manifest = json.load(archive.extractfile(first))
                    expected = {f['member']: f for f in manifest['payloads']}
                    seen = set()
                    for member in archive:
                        if member is first:
                            continue
                        if member.name not in expected or member.name in seen or not member.isfile():
                            raise RuntimeError('Remote tar member inventory differs')
                        record = expected[member.name]
                        with archive.extractfile(member) as source:
                            h = hashlib.file_digest(source, 'sha256').hexdigest()
                        if member.size != record['size_bytes'] or h != record['sha256']:
                            raise RuntimeError('Remote tar payload hash differs')
                        seen.add(member.name)
                    if seen != set(expected):
                        raise RuntimeError('Remote tar is missing payloads')
        emit('remote_download_verified', file=expected_path.name, bytes=restored.stat().st_size,
             sha256=digest)
    finally:
        if restored.exists():
            restored.unlink()


def record_for(entry, digest, location, status):
    return {'library_file_id': entry['library_file_id'], 'version_id': entry.get('version_id'),
            'library_path': entry['path'], 'original_name': entry['name'],
            'checkpoint': entry.get('checkpoint'), 'size_bytes': entry['size_bytes'],
            'sha256': digest, 'status': status, 'restore_from': location, 'recorded_at': now()}


def known_hashes(assets, state):
    result = {}
    byname = {}
    for a in assets:
        byname.setdefault(a['name'], []).append(a)
        if a['state'] == 'uploaded' and (a.get('digest') or '').startswith('sha256:'):
            result[(a['digest'][7:], a['size'])] = {
                'release_id': a['release_id'], 'asset_id': a['id'], 'asset': a['name'],
                'asset_sha256': a['digest'][7:], 'member': None}
    for name in ('earlier_sources_through93.json', 'earlier_sources_through115.json'):
        for source in json.loads((ROOT / name).read_text()):
            restore = source['restore_from']
            candidates = byname.get(restore['asset'], [])
            if len(candidates) != 1:
                continue
            a = candidates[0]
            if a['state'] != 'uploaded' or not (a.get('digest') or '').startswith('sha256:'):
                continue
            result[(source['sha256'], source.get('bytes', source.get('size_bytes')))] = {
                'release_id': a['release_id'], 'asset_id': a['id'], 'asset': a['name'],
                'asset_sha256': a['digest'][7:], 'member': restore['member'],
                'prior_catalog': name}
    for record in state['files'].values():
        result[(record['sha256'], record['size_bytes'])] = record['restore_from']
    return result


def source_path(entry):
    target = STAGE / entry['path'].lstrip('/')
    if not target.resolve().is_relative_to(STAGE.resolve()):
        raise RuntimeError('Source path escapes staging directory')
    return target


def reusable(entry):
    path = source_path(entry)
    if not path.is_file() or path.stat().st_size != entry['size_bytes']:
        return False
    try:
        return os.getxattr(path, 'user.library-file-id').decode() == entry['library_file_id']
    except OSError:
        return False


def materialize(entries, helper):
    missing = [e for e in entries if not reusable(e)]
    if not missing:
        return
    groups = {}
    for entry in missing:
        groups.setdefault((entry['list_page_file'], entry['list_page_index']), []).append(entry)
    if len(groups) > 1:
        for group in groups.values():
            materialize(group, helper)
        return
    page_file = missing[0]['list_page_file']
    page_index = missing[0]['list_page_index']
    if any(e['list_page_file'] != page_file or e['list_page_index'] != page_index for e in missing):
        raise RuntimeError('Library selection spans inventory pages')
    page = json.loads((ROOT / page_file).read_text())[page_index]
    selection = ''.join(f"{e['selection_index']:03d}" for e in missing)
    request = {'result': page, 'selection': selection,
               'destination': str(STAGE.relative_to(WORKSPACE))}
    emit('materialize_start', files=len(missing), bytes=sum(e['size_bytes'] for e in missing))
    result = subprocess.run([sys.executable, str(helper)], input=json.dumps(request),
                            capture_output=True, text=True, cwd=WORKSPACE, timeout=1800)
    (ROOT / 'last_download_stdout.txt').write_text(result.stdout)
    (ROOT / 'last_download_stderr.txt').write_text(result.stderr)
    if result.returncode:
        raise RuntimeError('Library materialization failed; outputs retained in last_download logs')
    output = json.loads(result.stdout)
    # Output files are authoritative; all must be the expected, private staging paths.
    actual = {str(Path(p).resolve()) for p in output['files']}
    expected = {str(source_path(e).resolve()) for e in missing}
    if actual != expected:
        raise RuntimeError('Unexpected Library materialization output paths')
    save(ROOT / 'last_download_result.json', output)
    for entry in missing:
        if not reusable(entry):
            raise RuntimeError('Library download size/identity verification failed')


def select_batch(queue, state, max_bytes):
    remaining = [e for e in queue if e['library_file_id'] not in state['files']]
    if not remaining:
        return []
    pending = RECEIPTS / f"Paper_I_All_Checkpoints_20261024_Batch_{len(state['batches']) + 1:03d}_Receipt.json"
    if pending.exists():
        ids = [r['library_file_id'] for r in json.loads(pending.read_text())['files']]
        byid = {e['library_file_id']: e for e in remaining}
        if any(i not in byid for i in ids):
            raise RuntimeError('Pending receipt and inventory state conflict')
        return [byid[i] for i in ids]
    batch = []
    size = 0
    for e in remaining:
        if len(batch) == 20 or (batch and size + e['size_bytes'] > max_bytes):
            break
        batch.append(e)
        size += e['size_bytes']
    return batch


def build_part(payloads, ordinal):
    temporary = PARTS / f'part-{ordinal:03d}.tar.zst'
    manifest = {'schema_version': 1, 'purpose': 'Byte-preserving checkpoint backup',
                'source_unchanged': True, 'lean_verification_claim': 'No new proof verification',
                'payloads': [{k: v for k, v in p.items() if k != 'local_path'} for p in payloads]}
    parameters = zstandard.ZstdCompressionParameters.from_level(9, window_log=30, enable_ldm=True)
    with temporary.open('wb') as raw, zstandard.ZstdCompressor(compression_params=parameters).stream_writer(raw) as writer:
        with tarfile.open(mode='w|', fileobj=writer) as archive:
            content = (json.dumps(manifest, indent=2, ensure_ascii=False) + '\n').encode()
            info = tarfile.TarInfo('BACKUP_MANIFEST.json')
            info.size = len(content)
            info.mode = 0o644
            archive.addfile(info, io.BytesIO(content))
            for payload in payloads:
                info = tarfile.TarInfo(payload['member'])
                info.size = payload['size_bytes']
                info.mode = 0o644
                with open(payload['local_path'], 'rb') as source:
                    archive.addfile(info, source)
    digest = sha256(temporary)
    final = PARTS / f'Paper_I_All_Checkpoints_20261024_Part_{ordinal:03d}_{digest[:12]}.tar.zst'
    temporary.rename(final)
    return final


def commit_receipt(state, receipt, receipt_asset, batch):
    receipt = {**receipt, 'receipt_asset': clean_asset(receipt_asset)}
    state['batches'].append({k: v for k, v in receipt.items() if k != 'files'})
    for record in receipt['files']:
        state['files'][record['library_file_id']] = record
    state['updated_at'] = now()
    save(STATE, state)
    for entry in batch:
        path = source_path(entry)
        if path.exists():
            if sha256(path) != state['files'][entry['library_file_id']]['sha256']:
                raise RuntimeError('Staging file changed; it was not removed')
            path.unlink()
    cleanup_verified_staging(state)


def cleanup_verified_staging(state):
    # Scratch copies may reappear while the workspace mirror finishes a transfer.
    # Only paths already verified and recorded in this backup are eligible.
    for record in state['files'].values():
        path = STAGE / record['library_path'].lstrip('/')
        if path.is_file() and path.stat().st_size == record['size_bytes'] and sha256(path) == record['sha256']:
            path.unlink()
        if path.parent.is_dir():
            prefix = '.' + path.name + '.'
            for temporary in list(path.parent.iterdir()):
                if temporary.name.startswith(prefix) and temporary.is_file():
                    temporary.unlink()


def resume_receipt(state, batch, ordinal):
    path = RECEIPTS / f'Paper_I_All_Checkpoints_20261024_Batch_{ordinal:03d}_Receipt.json'
    if not path.exists():
        return False
    receipt = json.loads(path.read_text())
    if {f['library_file_id'] for f in receipt['files']} != {e['library_file_id'] for e in batch}:
        raise RuntimeError('Pending receipt does not match the current batch')
    locations = {r['restore_from']['asset_id']: r['restore_from'] for r in receipt['files']}
    for location in locations.values():
        asset = api(f"repos/{REPO}/releases/assets/{location['asset_id']}")
        if asset['state'] != 'uploaded' or asset.get('digest') != 'sha256:' + location['asset_sha256']:
            raise RuntimeError('Pending receipt asset is not intact')
    receipt_asset = upload_exact(path)
    commit_receipt(state, receipt, receipt_asset, batch)
    for part in PARTS.glob(f'Paper_I_All_Checkpoints_20261024_Part_{ordinal:03d}_*'):
        if receipt['asset'] and sha256(part) == receipt['asset']['digest'][7:]:
            part.unlink()
    emit('pending_receipt_resumed', batch=ordinal, total_processed=len(state['files']))
    return True


def run(args):
    global UPLOAD_CONTEXT
    queue = json.loads((ROOT / 'upload_queue.json').read_text())['entries']
    for directory in (STAGE, PARTS, RECEIPTS):
        directory.mkdir(parents=True, exist_ok=True)
    state = json.loads(STATE.read_text()) if STATE.exists() else {
        'schema_version': 1, 'repository': REPO, 'release_id': RELEASE_ID,
        'status': 'IN_PROGRESS', 'files': {}, 'batches': [], 'started_at': now()}
    if args.plan:
        remaining = [e for e in queue if e['library_file_id'] not in state['files']]
        emit('plan', inventory_files=len(queue), processed=len(state['files']),
             remaining=len(remaining), remaining_source_bytes=sum(e['size_bytes'] for e in remaining),
             next_batch=[e['name'] for e in select_batch(queue, state, args.max_batch_bytes)])
        return
    account = api('user')['login']
    if account != 'jaehwoo':
        raise RuntimeError('Authenticated account is not jaehwoo; no upload attempted')
    assert_private_target()
    releases, assets = releases_and_assets()
    target_release = next(r for r in releases if r['id'] == RELEASE_ID)
    UPLOAD_CONTEXT = {'release': target_release, 'assets': [a for a in assets if a['release_id'] == RELEASE_ID]}
    baseline = ROOT / 'ALL_CHECKPOINTS_BASELINE_ASSETS.json'
    if not baseline.exists():
        save(baseline, [clean_asset(a) for a in assets])
    known = known_hashes(assets, state)
    cleanup_verified_staging(state)
    state.setdefault('uploader_versions', [])
    if SCRIPT_SHA256 not in state['uploader_versions']:
        state['uploader_versions'].append(SCRIPT_SHA256)
    save(STATE, state)
    executed = 0
    while batch := select_batch(queue, state, args.max_batch_bytes):
        ordinal = len(state['batches']) + 1
        if resume_receipt(state, batch, ordinal):
            known = known_hashes(assets, state)
            executed += 1
            if args.limit_batches and executed >= args.limit_batches:
                return
            continue
        source_bytes = sum(e['size_bytes'] for e in batch)
        already_staged = sum(e['size_bytes'] for e in batch if reusable(e))
        if shutil.disk_usage(ROOT).free < source_bytes * 3 - already_staged + 150_000_000:
            raise RuntimeError('Insufficient free space for staged source, ZIP, and fresh remote download')
        materialize(batch, args.helper)
        records = []
        payloads = []
        batch_hashes = {}
        for entry in batch:
            path = source_path(entry)
            digest = sha256(path)
            key = (digest, path.stat().st_size)
            if key in known:
                records.append(record_for(entry, digest, known[key], 'EXISTING_BYTES_MATCHED'))
            else:
                if key not in batch_hashes:
                    if Path(entry['name']).name != entry['name']:
                        raise RuntimeError('Original filename is not a basename')
                    member = 'originals/' + entry['library_file_id'] + '/' + entry['name']
                    if any(part in ('..', '') for part in member.split('/')):
                        raise RuntimeError('Invalid archive member name')
                    payloads.append({'member': member, 'original_name': entry['name'],
                                     'library_path': entry['path'], 'library_file_id': entry['library_file_id'],
                                     'size_bytes': path.stat().st_size, 'sha256': digest, 'local_path': str(path)})
                    batch_hashes[key] = member
                records.append(record_for(entry, digest, {'member': batch_hashes[key]}, 'NEW_REMOTE_BYTES_VERIFIED'))
        asset = None
        part = None
        assert_private_target()
        if payloads:
            part = build_part(payloads, ordinal)
            asset = upload_exact(part)
            fresh_download_verify(asset, part)
            for record in records:
                if record['status'] == 'NEW_REMOTE_BYTES_VERIFIED':
                    record['restore_from'].update({'release_id': RELEASE_ID, 'asset_id': asset['id'],
                        'asset': asset['name'], 'asset_sha256': asset['digest'][7:]})
        receipt = {'batch': ordinal, 'verified_at': now(), 'source_files': len(records),
                   'uploader_sha256': SCRIPT_SHA256,
                   'source_bytes': source_bytes, 'new_payload_files': len(payloads),
                   'asset': clean_asset(asset) if asset else None, 'files': records,
                   'verification': 'All staged originals SHA-256 checked. New backup container downloaded from GitHub; whole container and every stored original checked.'}
        receipt_path = RECEIPTS / f'Paper_I_All_Checkpoints_20261024_Batch_{ordinal:03d}_Receipt.json'
        save(receipt_path, receipt)
        receipt_asset = upload_exact(receipt_path)
        commit_receipt(state, receipt, receipt_asset, batch)
        for record in records:
            known[(record['sha256'], record['size_bytes'])] = record['restore_from']
        if part:
            part.unlink()
        emit('batch_complete', batch=ordinal, source_files=len(records),
             new_payload_files=len(payloads), total_processed=len(state['files']), inventory_files=len(queue))
        executed += 1
        if args.limit_batches and executed >= args.limit_batches:
            return
    assert_private_target()
    _, final_assets = releases_and_assets()
    current = {a['id']: clean_asset(a) for a in final_assets}
    baseline_assets = json.loads(baseline.read_text())
    if any(current.get(a['id']) != a for a in baseline_assets):
        raise RuntimeError('An earlier release asset changed during this run')
    state.update(status='ALL_INVENTORIED_ORIGINAL_BYTES_BACKED_UP', completed_at=now(),
                 inventory_file_count=len(queue), preexisting_assets_unchanged=True,
                 historical_unconfirmed_checkpoints=[72, 73, 74, 75],
                 manuscript_verification='INCOMPLETE; backup is not proof verification')
    save(STATE, state)
    emit('complete', files=len(state['files']), batches=len(state['batches']))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--helper', type=Path, required=True)
    parser.add_argument('--plan', action='store_true')
    parser.add_argument('--max-batch-bytes', type=int, default=650_000_000)
    parser.add_argument('--limit-batches', type=int)
    args = parser.parse_args()
    try:
        run(args)
    except Exception as error:
        emit('stopped', error=type(error).__name__, detail=str(error))
        raise


if __name__ == '__main__':
    main()
