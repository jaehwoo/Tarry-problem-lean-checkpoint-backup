"""Reconstruct and verify checkpoint211 artifacts; this does not run Lean proofs.

Input is the exact checkpoint210 archive and a content-addressed211 overlay.
All inherited members, including inactive transfer copies, are preserved.
"""
from pathlib import Path
import argparse,base64,csv,hashlib,io,json,tarfile,zipfile
import zstandard

def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def rawsha(b):return hashlib.sha256(b).hexdigest()
def jwrite(p,v):p.write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n')
def members(archive):
    with archive.open('rb') as f:
        with zstandard.ZstdDecompressor().stream_reader(f) as d:
            with tarfile.open(fileobj=d,mode='r|') as t:
                for m in t:
                    assert m.isfile() and m.name.startswith('PaperILean/')
                    rel=m.name.removeprefix('PaperILean/')
                    assert rel and not rel.startswith('/') and '..' not in Path(rel).parts
                    f=t.extractfile(m);f.archive_mode=m.mode
                    yield rel,m.size,f
def zipwrite(path,files):
    with zipfile.ZipFile(path,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
        for name,source in sorted(files.items()):
            i=zipfile.ZipInfo(name,(2026,10,25,0,0,0));i.compress_type=zipfile.ZIP_DEFLATED
            i.external_attr=0o100644<<16;z.writestr(i,source.read_bytes())

def reconstruct(stage,parent,out):
    compressed=stage/'RECONSTRUCTION.json.zst.b64'
    recipe=json.loads(zstandard.ZstdDecompressor().decompress(base64.b64decode(compressed.read_bytes()))) if compressed.exists() else json.loads((stage/'RECONSTRUCTION.json').read_text())
    assert sha(parent)==recipe['parent_archive_sha256']
    out.mkdir(parents=True,exist_ok=True);overlay=out/'overlay';overlay.mkdir(exist_ok=True)
    for r in recipe['payload']:
        raw=b''.join((stage/p).read_bytes() for p in r['chunks'])
        b=zstandard.ZstdDecompressor().decompress(base64.b64decode(raw))
        assert len(b)==r['bytes'] and rawsha(b)==r['sha256'],r['path']
        p=overlay/r['path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
    required={'reports/MasterChecklist.json','reports/Checkpoint210_KernelProjectDependencies.json',
        'reports/PublishedAssumptions_Contracts.json','reports/PublishedAssumptions_ConditionalDeclarations.json',
        'reports/PublishedAssumptions_ConditionalDeclarations.csv'}
    inherited={}
    for rel,size,f in members(parent):
        if rel in required:inherited[rel]=f.read()
        if inherited.keys()==required:break
    assert inherited.keys()==required
    snap=json.loads((overlay/'tools/checkpoint211_parent_snapshot_recipe.json').read_text())
    p=overlay/'history/checkpoint210_before211/CanonicalCheckpoint210.zip';p.parent.mkdir(parents=True,exist_ok=True)
    if not p.exists():
        # Optional exact rebuild for the recorded zlib version; normally the
        # immutable snapshot is shipped verbatim to avoid compressor differences.
        with zipfile.ZipFile(p,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=snap['compression_level']) as z:
            z.comment=bytes.fromhex(snap['comment_hex'])
            for a in snap['entries']:
                i=zipfile.ZipInfo(a['filename'],tuple(a['date_time']))
                for k in ['compress_type','create_system','create_version','extract_version','flag_bits','volume','internal_attr','external_attr']:setattr(i,k,a[k])
                i.comment=bytes.fromhex(a['comment_hex']);i.extra=bytes.fromhex(a['extra_hex'])
                z.writestr(i,inherited['reports/'+i.filename],compress_type=i.compress_type,compresslevel=snap['compression_level'])
    master=json.loads(inherited['reports/MasterChecklist.json'])
    patch=json.loads((overlay/'reports/Checkpoint211_MasterChecklistPatch.json').read_text())
    assert sha(p)==patch['parent_snapshot_sha256']
    master['items']=[patch['modified_rows'].get(r['id'],r) for r in master['items']]+patch['added_rows']
    master.update(patch['top_level_updates'])
    master['main_dependency_graph']=[dict(id=r['id'],dependencies=r.get('dependencies','')) for r in master['items']]
    p=overlay/'reports/MasterChecklist.json';p.write_text(json.dumps(master,separators=(',',':'),ensure_ascii=False)+'\n')
    assert sha(p)==patch['expected_full_master_sha256']
    fields=['id','kind','status','declaration','source_location','source_lines','dependencies','blocker_category','exact_unresolved_statement','next_concrete_task']
    with (overlay/'reports/MasterChecklist.csv').open('w') as f:
        w=csv.DictWriter(f,fieldnames=fields,extrasaction='ignore');w.writeheader()
        for r in master['items']:w.writerow({k:json.dumps(r[k],ensure_ascii=False) if isinstance(r.get(k),(dict,list)) else r.get(k,'') for k in fields})
    kernel=json.loads(inherited['reports/Checkpoint210_KernelProjectDependencies.json'])+recipe['kernel_append']
    jwrite(overlay/'reports/Checkpoint211_KernelProjectDependencies.json',kernel)
    for r in recipe['changed_files']:
        p=overlay/r['path'];assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],r['path']
    changes={r['path']:r for r in recipe['changed_files']}
    expected={r['path']:r for r in recipe['parent_files']};expected.update(changes)
    archive=out/'Paper_I_Lean_Checkpoint_211_Original_Route.tar.zst'
    seen=set()
    class Checked:
        def __init__(self,f):self.f=f;self.h=hashlib.sha256()
        def read(self,n=-1):
            b=self.f.read(n);self.h.update(b);return b
    def add(t,rel,size,f,mode=0o644):
        i=tarfile.TarInfo('PaperILean/'+rel);i.size=size;i.mode=mode;i.mtime=0
        wrapped=Checked(f);t.addfile(i,wrapped);return wrapped.h.hexdigest()
    with archive.open('wb') as raw:
        with zstandard.ZstdCompressor(level=6,threads=2).stream_writer(raw) as z:
            with tarfile.open(fileobj=z,mode='w|') as t:
                for rel,size,f in members(parent):
                    assert rel not in seen;seen.add(rel)
                    original_mode=f.archive_mode
                    # Parent archive SHA is fixed; all unchanged member hashes are checked below.
                    if rel in changes:
                        p=overlay/rel
                        with p.open('rb') as src:h=add(t,rel,p.stat().st_size,src,original_mode)
                    else:h=add(t,rel,size,f,original_mode)
                    assert h==expected[rel]['sha256'],rel
                for rel in sorted(set(changes)-seen):
                    p=overlay/rel
                    with p.open('rb') as f:assert add(t,rel,p.stat().st_size,f)==changes[rel]['sha256']
    assert seen=={r['path'] for r in recipe['parent_files']}
    manifest={'checkpoint':211,'scope':'Full preserved project, including all inherited inactive copies; runtime and rebuildable cache excluded.',
              'parent_archive_sha256':recipe['parent_archive_sha256'],'files':[expected[k] for k in sorted(expected)]}
    jwrite(out/'Paper_I_Lean_Checkpoint_211_Manifest.json',manifest)
    # Fresh stream verification of every packaged member, not a proof re-execution.
    checked={}
    for rel,size,f in members(archive):
        h=hashlib.file_digest(f,'sha256').hexdigest();assert size==expected[rel]['bytes'] and h==expected[rel]['sha256'],rel
        assert rel not in checked;checked[rel]=h
    assert set(checked)==set(expected)
    for name,src in {'Paper_I_Lean_Checkpoint_211_Correspondence.md':'reports/CorrespondenceReport.md',
                     'Paper_I_Lean_Checkpoint_211_Verification_Summary.json':'evidence/checkpoint_211_final_verification_summary.json'}.items():
        (out/name).write_bytes((overlay/src).read_bytes())
    zipwrite(out/'Paper_I_Lean_Checkpoint_211_Checklist.zip',{p:(overlay/p) for p in ['reports/MasterChecklist.json','reports/MasterChecklist.csv','reports/MasterChecklist.md','reports/Checkpoint211_MasterChecklistPatch.json']})
    zipwrite(out/'Paper_I_Lean_Checkpoint_211_Build_Evidence.zip',{r['path']:overlay/r['path'] for r in recipe['changed_files'] if r['path'].startswith(('evidence/','reports/','tools/')) and r['path'] not in ['reports/MasterChecklist.json','reports/MasterChecklist.csv']})
    zipwrite(out/'Paper_I_Lean_Checkpoint_211_New_Lean_Sources.zip',{r['path']:overlay/r['path'] for r in recipe['changed_files'] if r['path'].endswith('.lean') or r['path'].startswith('tools/checkpoint211_')})
    assets=[dict(path=p.name,bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(out.glob('Paper_I_Lean_Checkpoint_211_*')) if p.is_file()]
    receipt={'checkpoint':211,'scope':'Packaging and fresh archive readback, not an additional Lean run. Local executed build/audit evidence is included.',
             'parent_files':len(seen),'current_files':len(expected),'all_parent_paths_retained':True,'all_member_sha256_checked':True,
             'full_manuscript_verification_complete':False,'artifacts':assets}
    jwrite(out/'Paper_I_Lean_Checkpoint_211_Packaging_Receipt.json',receipt)
    (out/'SHA256SUMS.txt').write_text(''.join(r['sha256']+'  '+r['path']+'\n' for r in assets))
    print(json.dumps(receipt,indent=2),flush=True)
    return receipt

if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('stage',type=Path);a.add_argument('parent',type=Path);a.add_argument('output',type=Path)
    v=a.parse_args();reconstruct(v.stage,v.parent,v.output)
