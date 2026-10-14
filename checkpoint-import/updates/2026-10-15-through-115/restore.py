#!/usr/bin/env python3
"""Verify private release assets or restore a checkpoint without executing it."""
import argparse, collections, gzip, hashlib, json, lzma, stat, tempfile, zipfile
from pathlib import Path, PurePosixPath

CATALOG = Path(__file__).resolve().parent

def sha_file(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()

def copy_checked(reader, expected, output=None):
    h = hashlib.sha256()
    size = 0
    while data := reader.read(1024 * 1024):
        h.update(data)
        size += len(data)
        if output is not None:
            output.write(data)
    if h.hexdigest() != expected['sha256'] or size != expected.get('bytes', expected.get('size_bytes')):
        raise ValueError('Hash or byte count mismatch')

def source_reader(source, assets, output):
    location = source['restore_from']
    path = assets / location['asset']
    if location['member'] is None:
        with path.open('rb') as f:
            copy_checked(f, source, output)
    else:
        with zipfile.ZipFile(path) as z, z.open(location['member']) as f:
            copy_checked(f, source, output)

def verify(assets, sources, specs):
    for item in specs:
        path = assets / item['name']
        if path.stat().st_size != item['bytes'] or sha_file(path) != item['sha256']:
            raise ValueError('Asset mismatch: ' + item['name'])
    for source in sources:
        source_reader(source, assets, None)
    return {'status': 'ASSETS_AND_SOURCE_BYTES_VERIFIED', 'assets': len(specs), 'source_files': len(sources)}

def restore(assets, sources, coverage, number, destination, audit_spec):
    options = coverage['checkpoint_archives'].get(str(number))
    if not options:
        raise ValueError('No preserved checkpoint archive for this number')
    destination = destination.resolve()
    if destination.exists():
        raise ValueError('Destination must not exist')
    if assets.resolve() == destination or destination in assets.resolve().parents:
        raise ValueError('Destination overlaps assets')
    audit_path = assets / audit_spec['name']
    if sha_file(audit_path) != audit_spec['sha256']:
        raise ValueError('Archive audit mismatch')
    audit = json.loads(gzip.decompress(audit_path.read_bytes()))['archives']
    target = options[0]['archive_sha256']
    paths = {s['sha256']: (s, []) for s in sources}
    queue = collections.deque(paths)
    while target not in paths and queue:
        parent = queue.popleft()
        for member in audit.get(parent, {}).get('members', []):
            child = member['sha256']
            if child in audit and child not in paths:
                source, steps = paths[parent]
                paths[child] = (source, steps + [(parent, member)])
                queue.append(child)
    if target not in paths:
        raise ValueError('No verified route to checkpoint')
    source, steps = paths[target]
    destination.mkdir(parents=True)
    with tempfile.TemporaryDirectory(prefix='restore-', dir=destination) as temp:
        current = Path(temp) / 'source.archive'
        with current.open('xb') as out:
            source_reader(source, assets, out)
        for idx, (parent, member) in enumerate(steps):
            next_path = Path(temp) / f'{idx}.archive'
            with next_path.open('xb') as out:
                if audit[parent].get('format') == 'xz':
                    with lzma.open(current, 'rb') as f:
                        copy_checked(f, member, out)
                else:
                    with zipfile.ZipFile(current) as z, z.open(member['path']) as f:
                        copy_checked(f, member, out)
            current.unlink()
            current = next_path
        expected = {m['path']: m for m in audit[target]['members']}
        restored = []
        with zipfile.ZipFile(current) as z:
            actual = [i.filename for i in z.infolist() if not i.is_dir()]
            if len(actual) != len(set(actual)) or set(actual) != set(expected):
                raise ValueError('Member inventory mismatch')
            for item in z.infolist():
                relative = PurePosixPath(item.filename)
                if relative.is_absolute() or '..' in relative.parts or '\\' in item.filename:
                    raise ValueError('Unsafe path')
                path = destination.joinpath(*relative.parts)
                if item.is_dir():
                    path.mkdir(parents=True, exist_ok=True)
                    continue
                mode = item.external_attr >> 16
                if stat.S_IFMT(mode) not in (0, stat.S_IFREG):
                    raise ValueError('Unsupported archive member type')
                path.parent.mkdir(parents=True, exist_ok=True)
                with z.open(item) as f, path.open('xb') as out:
                    copy_checked(f, expected[item.filename], out)
                if sha_file(path) != expected[item.filename]['sha256']:
                    raise ValueError('Disk readback mismatch')
                if mode & 0o777:
                    path.chmod(mode & 0o777)
                restored.append(item.filename)
    result = {'status': 'CHECKPOINT_RESTORE_BYTES_VERIFIED', 'checkpoint': number,
              'archive_sha256': target, 'files': len(restored),
              'lean_files': sum(n.endswith('.lean') for n in restored),
              'verification_scope': 'File integrity only; no Lean compilation or theorem verification.'}
    (destination / 'RESTORE_RECEIPT.json').write_text(json.dumps(result, indent=2) + '\n')
    return result

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['verify', 'restore'])
    parser.add_argument('--assets', type=Path, required=True)
    parser.add_argument('--checkpoint', type=int)
    parser.add_argument('--destination', type=Path)
    args = parser.parse_args()
    sources = json.loads((CATALOG / 'sources.json').read_text())
    specs = json.loads((CATALOG / 'assets.json').read_text())
    if args.command == 'verify':
        result = verify(args.assets, sources, specs)
    else:
        if args.checkpoint is None or args.destination is None:
            parser.error('restore needs --checkpoint and --destination')
        coverage = json.loads((CATALOG / 'coverage.json').read_text())
        audit_spec = next(a for a in specs if a['kind'] == 'archive_member_audit')
        result = restore(args.assets, sources, coverage, args.checkpoint, args.destination, audit_spec)
    print(json.dumps(result, ensure_ascii=False, indent=2))

if __name__ == '__main__':
    main()

