import collections, gzip, hashlib, json, lzma, re, shutil, stat, tempfile, zipfile
from pathlib import Path, PurePosixPath
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'new-import'
OUT.mkdir(exist_ok=True)
ASSETS = ROOT / 'upload-assets'
ASSETS.mkdir(exist_ok=True)

def dump(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')

def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()

def main():
    listed = json.load(open(ROOT / 'evidence/library_initial_inventory.json'))['structuredContent']['items']
    metadata = {str(ROOT / 'sources' / x['path'].lstrip('/')): x for x in listed}
    downloaded = json.load(open(ROOT / 'evidence/download_result.json'))['files']
    old = json.loads(json.load(open(ROOT / 'evidence/historical_coverage.json'))['structuredContent']['content'])
    known_old = {x['archive_sha256'] for opts in old['checkpoint_archives'].values() for x in opts}
    prior = json.loads(json.load(open(ROOT / 'evidence/historical_source_provenance.json'))['structuredContent']['content'])
    known_prior = {x['file_id']: x for x in prior}
    sources = []
    for fn in downloaded:
        p = Path(fn)
        m = metadata[fn]
        digest = sha(p)
        assert p.stat().st_size == m['size_bytes'], p
        if m['file_id'] in known_prior:
            assert digest == known_prior[m['file_id']]['sha256'], p
        n = m['name']
        kind = 'progress' if 'Progress' in n or 'Working_' in n else 'delivery_verification' if 'Delivery_Verification' in n else 'build_evidence' if 'Build_Evidence' in n else 'checklist' if 'Checklist' in n else 'report' if 'Report' in n else 'project_candidate'
        sources.append({'name': n, 'path': m['path'], 'sha256': digest, 'bytes': p.stat().st_size, 'kind': kind, 'library_file_id': m['library_file_id'], 'file_id': m['file_id'], 'version_id': m['version_id'], 'created_at': m['created_at'], 'modified_at': m['modified_at'], 'local_path': fn})
    dump('source_provenance.json', sources)
    archives = {}
    complete = collections.defaultdict(list)
    progress = collections.defaultdict(list)
    seen = set()
    def inspect(path, digest, label, route):
        if digest in seen or digest in known_old:
            return
        seen.add(digest)
        print('SCAN', label, path.stat().st_size, flush=True)
        if label.endswith('.xz'):
            # Preserve the compressed bytes and audit the decompressed container.
            with tempfile.NamedTemporaryFile(dir=ROOT, suffix='.zip') as tmp:
                h = hashlib.sha256(); size = 0
                with lzma.open(path, 'rb') as f:
                    while data := f.read(1024 * 1024):
                        tmp.write(data); h.update(data); size += len(data)
                tmp.flush()
                child = {'path': label[:-3], 'sha256': h.hexdigest(), 'bytes': size}
                archives[digest] = {'format': 'xz', 'name': label, 'members': [child]}
                if zipfile.is_zipfile(tmp.name):
                    inspect(Path(tmp.name), h.hexdigest(), label[:-3], route + [child['path']])
                else:
                    archives[digest]['note'] = 'Decompressed member preserved; not treated as a ZIP project.'
            return
        with zipfile.ZipFile(path) as z:
            names = z.namelist()
            assert len(names) == len(set(names)), ('duplicate ZIP member', label)
            record = {'format': 'zip', 'name': label, 'route': route, 'members': []}
            archives[digest] = record
            nested = []
            for info in z.infolist():
                pp = PurePosixPath(info.filename)
                assert not pp.is_absolute() and '..' not in pp.parts and '\\' not in info.filename, info.filename
                if info.is_dir():
                    continue
                assert stat.S_IFMT(info.external_attr >> 16) in (0, stat.S_IFREG), info.filename
                h = hashlib.sha256(); size = 0
                with z.open(info) as f:
                    while data := f.read(1024 * 1024):
                        h.update(data); size += len(data)
                assert size == info.file_size
                member = {'path': info.filename, 'sha256': h.hexdigest(), 'bytes': size}
                record['members'].append(member)
                if info.filename.endswith(('.zip', '.zip.xz')) and h.hexdigest() not in known_old:
                    nested.append(member)
            roots = [n[:-len('lean-toolchain')] for n in names if n.endswith('lean-toolchain') and '/history/' not in n and '/executed_sources/' not in n]
            main_root = 'PaperILean/' if 'PaperILean/' in roots else roots[0] if roots else None
            checks = {}
            if main_root:
                checks = {key: main_root+val in names for key,val in {'toolchain':'lean-toolchain','lake_manifest':'lake-manifest.json','root':'PaperILean.lean','checklist':'reports/MasterChecklist.json','correspondence':'reports/CorrespondenceReport.md'}.items()}
                checks['lakefile'] = any(main_root+v in names for v in ['lakefile.lean','lakefile.toml'])
                checks['lean_sources'] = any(n.startswith(main_root+'PaperILean/') and n.endswith('.lean') for n in names)
                checks['manuscripts'] = any(n.startswith(main_root+'manuscript/') and n.endswith('.tex') for n in names)
                record['project_checks'] = checks
                record['readme_excerpt'] = z.read(main_root+'README.md').decode('utf-8')[:1200] if main_root+'README.md' in names else None
            match = re.search(r'Checkpoint_(\d+)', label)
            number = int(match.group(1)) if match else None
            if number and number > 93:
                option = {'archive_sha256': digest, 'archive_name': label, 'lean_files': sum(n.endswith('.lean') for n in names), 'project_checks': checks, 'route': route}
                if 'Progress' in label or 'Working_' in label:
                    progress[str(number)].append(option)
                elif re.fullmatch(r'Paper_I_Lean_(?:History_)?Checkpoint_\d+(?:_Joint_Selection)?\.zip', label) and checks and all(checks.values()):
                    complete[str(number)].append(option)
                elif re.fullmatch(r'Paper_I_Lean_(?:History_)?Checkpoint_\d+(?:_Joint_Selection)?\.zip', label):
                    record['classification_warning'] = 'Project-named archive fails one or more required structure checks.'
            for member in nested:
                if member['sha256'] in seen:
                    continue
                with tempfile.NamedTemporaryFile(dir=ROOT, suffix='.archive') as tmp:
                    with z.open(member['path']) as f:
                        shutil.copyfileobj(f, tmp, 1024 * 1024)
                    tmp.flush()
                    inspect(Path(tmp.name), member['sha256'], PurePosixPath(member['path']).name, route + [member['path']])
    for src in sources:
        inspect(Path(src['local_path']), src['sha256'], src['name'], [src['path']])
    audit = {'archives': archives, 'known_historical_archive_hashes_reused': sorted(known_old), 'scope': 'ZIP member CRC/size/SHA-256 and structure; not Lean compilation or theorem verification.'}
    audit_path = ASSETS / 'Paper_I_Newer_Archive_Audit.json.gz'
    with gzip.GzipFile(filename=str(audit_path),mode='wb',mtime=0) as f:
        f.write(json.dumps(audit,ensure_ascii=False,separators=(',',':')).encode())
    all_numbers = sorted(set(map(int, old['checkpoint_archives'])) | set(map(int, complete)))
    coverage = {'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'checkpoint_archives':dict(complete), 'progress_archives':dict(progress), 'complete_project_numbers':sorted(map(int,complete)), 'cumulative_preserved_numbers':all_numbers, 'missing_complete_checkpoint_numbers':[n for n in range(1,max(all_numbers)+1) if n not in all_numbers], 'historical_coverage_source':'checkpoint-import/coverage.json at b1b83e60a556733b8b257446c0131cc3a38f35c7', 'number_1_convention':old.get('number_1_convention'), 'definition_of_complete':'A completed checkpoint package with sources, pins, manuscripts, checklist, correspondence and recorded evidence; does not mean the manuscript is fully proved or provide toolchain/cache binaries.', 'verification_scope':'Byte preservation, archive integrity and restoration only.'}
    dump('coverage.json',coverage)
    specs = []
    # Independent ZIP containers; original files are stored byte-for-byte.
    batches = [[]]; size = 0
    for src in sorted(sources, key=lambda s:s['path']):
        if size + src['bytes'] > 700_000_000 and batches[-1]:
            batches.append([]); size=0
        batches[-1].append(src); size+=src['bytes']
    for idx,batch in enumerate(batches,1):
        name=f'Paper_I_Newer_Originals_Part_{idx:02d}.zip'
        dest=ASSETS/name
        with zipfile.ZipFile(dest,'w',compression=zipfile.ZIP_STORED,allowZip64=True) as z:
            for src in batch:
                member='originals'+src['path']
                z.write(src['local_path'],member)
                src['restore_from']={'asset':name,'member':member}
                src.pop('local_path')
        specs.append({'name':name,'bytes':dest.stat().st_size,'sha256':sha(dest),'kind':'original_archives'})
    specs.append({'name':audit_path.name,'bytes':audit_path.stat().st_size,'sha256':sha(audit_path),'kind':'archive_member_audit'})
    dump('sources.json',sources)
    dump('assets.json',specs)
    (OUT/'SHA256SUMS').write_text(''.join(x['sha256']+'  '+x['name']+'\n' for x in specs))
    shutil.copyfile(ROOT/'existing-tools/restore.py',OUT/'restore.py')
    print(json.dumps({'sources':len(sources),'source_bytes':sum(s['bytes'] for s in sources),'audited_archives':len(archives),'complete_numbers':coverage['complete_project_numbers'],'gaps':coverage['missing_complete_checkpoint_numbers'],'assets':specs},indent=2),flush=True)

if __name__=='__main__':
    main()
