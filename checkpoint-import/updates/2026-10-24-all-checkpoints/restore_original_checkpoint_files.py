#!/usr/bin/env python3
"""Restore byte-identical original artifacts from the all-checkpoint catalog.

This restores the saved original archives and companion files. It does not
replace their own instructions for assembling an incremental Lean checkpoint.
No Lean compilation or manuscript-verification claim is made.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import zipfile

import zstandard

REPO = 'jaehwoo/lean-checkpoint-backup'
REPO_ID = 1417233863


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def api(gh, endpoint, *, output=None):
    cmd = [gh, 'api', endpoint]
    if output is not None:
        cmd += ['-H', 'Accept: application/octet-stream']
    result = subprocess.run(cmd, stdout=output or subprocess.PIPE, stderr=subprocess.PIPE, timeout=1800)
    if result.returncode:
        raise RuntimeError(result.stderr.decode('utf-8', 'replace')[-2000:])
    return json.loads(result.stdout) if output is None else None


def destination_path(destination, record):
    relative = Path(record['library_path'].lstrip('/'))
    if relative.is_absolute() or '..' in relative.parts or not relative.parts:
        raise RuntimeError('Unsafe original path in catalog')
    result = destination / relative
    if not result.resolve().is_relative_to(destination.resolve()):
        raise RuntimeError('Restore path escapes destination')
    return result


def copy_checked(source, record, destination):
    target = destination_path(destination, record)
    target.parent.mkdir(parents=True, exist_ok=True)
    temporary = target.with_name(target.name + '.partial')
    if target.exists() or temporary.exists():
        raise RuntimeError(f'Refusing to overwrite {target}')
    h = hashlib.sha256()
    count = 0
    try:
        with temporary.open('xb') as out:
            while chunk := source.read(4 * 1024 * 1024):
                out.write(chunk)
                h.update(chunk)
                count += len(chunk)
            out.flush()
            os.fsync(out.fileno())
        if count != record['size_bytes'] or h.hexdigest() != record['sha256']:
            raise RuntimeError(f'Restored bytes do not match {record["original_name"]}')
        temporary.rename(target)
        if digest(target) != record['sha256']:
            raise RuntimeError('Restored disk readback differs')
        return {'library_file_id': record['library_file_id'], 'path': str(target),
                'size_bytes': count, 'sha256': h.hexdigest(), 'disk_readback_matched': True}
    finally:
        if temporary.exists():
            temporary.unlink()


def obtain_asset(gh, assets, location, allow_download):
    path = assets / str(location['asset_id']) / location['asset']
    flat = assets / location['asset']
    if not path.exists() and flat.is_file():
        path = flat
    if not path.exists():
        if not allow_download:
            raise RuntimeError(f'Missing asset {location["asset"]}; supply it or use --download')
        path.parent.mkdir(parents=True, exist_ok=True)
        temporary = path.with_name(path.name + '.partial')
        try:
            with temporary.open('wb') as out:
                api(gh, f'repos/{REPO}/releases/assets/{location["asset_id"]}', output=out)
            if digest(temporary) != location['asset_sha256']:
                raise RuntimeError('Downloaded asset hash differs from catalog')
            temporary.rename(path)
        finally:
            if temporary.exists():
                temporary.unlink()
    if digest(path) != location['asset_sha256']:
        raise RuntimeError(f'Asset hash differs: {path.name}')
    return path


def restore_group(path, records, destination):
    result = []
    direct = [r for r in records if r['restore_from']['member'] is None]
    for record in direct:
        with path.open('rb') as source:
            result.append(copy_checked(source, record, destination))
    nested = [r for r in records if r['restore_from']['member'] is not None]
    wanted = {}
    for record in nested:
        wanted.setdefault(record['restore_from']['member'], []).append(record)
    if not wanted:
        return result
    if path.suffix == '.zip':
        with zipfile.ZipFile(path) as archive:
            for name, entries in wanted.items():
                for record in entries:
                    with archive.open(name) as source:
                        result.append(copy_checked(source, record, destination))
    elif path.name.endswith('.tar.zst'):
        with path.open('rb') as raw:
            header = raw.read(18)
        if zstandard.get_frame_parameters(header).window_size > (1 << 30):
            raise RuntimeError('Compression window exceeds supported 1 GiB')
        seen = set()
        with path.open('rb') as raw, zstandard.ZstdDecompressor(max_window_size=1 << 30).stream_reader(raw) as reader:
            with tarfile.open(mode='r|', fileobj=reader) as archive:
                for member in archive:
                    if member.name not in wanted:
                        continue
                    if not member.isfile() or member.name in seen:
                        raise RuntimeError('Invalid or duplicate selected archive member')
                    entries = wanted[member.name]
                    first = entries[0]
                    with archive.extractfile(member) as source:
                        result.append(copy_checked(source, first, destination))
                    for record in entries[1:]:
                        with destination_path(destination, first).open('rb') as source:
                            result.append(copy_checked(source, record, destination))
                    seen.add(member.name)
        if seen != set(wanted):
            raise RuntimeError('A requested original is missing from the tar archive')
    else:
        raise RuntimeError('Unsupported enclosing archive format')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--catalog', type=Path, required=True)
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument('--checkpoint', type=int)
    selection.add_argument('--all', action='store_true')
    parser.add_argument('--assets', type=Path, required=True)
    parser.add_argument('--destination', type=Path, required=True)
    parser.add_argument('--download', action='store_true')
    parser.add_argument('--gh', default='gh')
    args = parser.parse_args()
    catalog = json.loads(args.catalog.read_text())
    if catalog['repository'] != REPO:
        raise RuntimeError('Unexpected backup repository')
    if args.all and catalog['status'] != 'ALL_INVENTORIED_ORIGINAL_BYTES_BACKED_UP':
        raise RuntimeError('The catalog is incomplete; a full restore is not certified')
    records = [r for r in catalog['files'].values() if args.all or r.get('checkpoint') == args.checkpoint]
    if not records:
        raise RuntimeError('No original artifacts for that checkpoint in this catalog; see the earlier history catalog')
    if args.destination.exists():
        raise RuntimeError('Restore destination must not already exist')
    paths = [destination_path(args.destination, r) for r in records]
    if len(paths) != len(set(paths)):
        raise RuntimeError('Selected records have conflicting original paths')
    if args.download:
        repo = api(args.gh, f'repos/{REPO}')
        if repo['id'] != REPO_ID or not repo['private']:
            raise RuntimeError('Repository identity or visibility differs')
    groups = {}
    for record in records:
        groups.setdefault(record['restore_from']['asset_id'], []).append(record)
    args.destination.mkdir(parents=True)
    restored = []
    for entries in groups.values():
        location = entries[0]['restore_from']
        path = obtain_asset(args.gh, args.assets, location, args.download)
        restored.extend(restore_group(path, entries, args.destination))
    receipt = {'status': 'ORIGINAL_ARTIFACT_RESTORE_VERIFIED',
               'verified_at': dt.datetime.now(dt.timezone.utc).isoformat(),
               'checkpoint': args.checkpoint, 'selected_files': len(records),
               'restored_files': len(restored), 'total_bytes': sum(r['size_bytes'] for r in restored),
               'files': restored, 'lean_build_performed': False,
               'scope': 'Original artifact bytes and disk readback; follow original instructions to assemble the Lean project'}
    (args.destination / 'RESTORE_RECEIPT.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'files'}), flush=True)


if __name__ == '__main__':
    main()
