#!/usr/bin/env python3
"""Restore exact 71/76 bytes to fresh paths, then compare; never reconstruct 72–75."""
import difflib,hashlib,json,stat,zipfile
from pathlib import Path,PurePosixPath
ROOT=Path(__file__).resolve().parent
OUT=ROOT/'investigation'

def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()

coverage=json.loads((ROOT/'baseline/coverage.json').read_text())
manifests={}
for n in (71,76):
    archive=OUT/f'original_checkpoint_{n}.zip'
    expected=coverage['checkpoint_archives'][str(n)][0]['archive_sha256']
    assert sha(archive)==expected
    dest=ROOT/'restored'/f'checkpoint_{n}'
    if dest.exists():raise RuntimeError('Refusing existing destination: '+str(dest))
    dest.mkdir(parents=True)
    members={}
    with zipfile.ZipFile(archive) as z:
        for info in z.infolist():
            rel=PurePosixPath(info.filename)
            if rel.is_absolute() or '..' in rel.parts or '\\' in info.filename:raise ValueError('Unsafe path')
            mode=info.external_attr>>16
            if info.is_dir():continue
            if stat.S_IFMT(mode) not in (0,stat.S_IFREG):raise ValueError('Unsupported file type')
            if info.filename in members:raise ValueError('Duplicate member')
            p=dest.joinpath(*rel.parts);p.parent.mkdir(parents=True,exist_ok=True)
            h=hashlib.sha256();size=0
            with z.open(info) as f,p.open('xb') as o:
                while b:=f.read(1024*1024):o.write(b);h.update(b);size+=len(b)
            assert size==info.file_size and sha(p)==h.hexdigest()
            members[info.filename]={'sha256':h.hexdigest(),'bytes':size}
    receipt={'checkpoint':n,'archive_sha256':expected,'destination':str(dest),'files':len(members),'lean_paths':sum(x.endswith('.lean') for x in members),'status':'ALL_RESTORED_FILES_READBACK_SHA256_MATCHED','scope':'Archive byte integrity and restored file equality only; no Lean compilation or mathematical verification.','members':members}
    (OUT/f'restored_{n}_manifest.json').write_text(json.dumps(receipt,indent=2)+'\n')
    manifests[n]=members

a,b=manifests[71],manifests[76]
unchanged=sorted(k for k in a.keys()&b.keys() if a[k]==b[k])
changed=sorted(k for k in a.keys()&b.keys() if a[k]!=b[k])
added=sorted(b.keys()-a.keys());removed=sorted(a.keys()-b.keys())
old_by_hash={}
for k,v in a.items():old_by_hash.setdefault(v['sha256'],[]).append(k)
aliases=[{'new_path':k,'same_bytes_in_71':old_by_hash[b[k]['sha256']]} for k in added if b[k]['sha256'] in old_by_hash]
active=lambda k:k.startswith('PaperILean/PaperILean/') and k.endswith('.lean') and k.count('/')==2
diff={'schema':1,'from_checkpoint':71,'to_checkpoint':76,'counts':{'from_files':len(a),'to_files':len(b),'unchanged':len(unchanged),'changed':len(changed),'added':len(added),'removed':len(removed)},'active_lean_counts':{'from':sum(map(active,a)),'to':sum(map(active,b)),'unchanged':sum(map(active,unchanged)),'changed':sum(map(active,changed)),'added':sum(map(active,added)),'removed':sum(map(active,removed))},'unchanged':unchanged,'changed':[{'path':k,'before':a[k],'after':b[k]} for k in changed],'added':[{'path':k,**b[k]} for k in added],'removed':[{'path':k,**a[k]} for k in removed],'added_content_aliases':aliases,'active_lean_added':[k for k in added if active(k)],'active_lean_changed':[k for k in changed if active(k)],'manuscripts':[{'path':k,'sha256_before':a[k]['sha256'],'sha256_after':b.get(k,{}).get('sha256'),'equal':a[k]==b.get(k)} for k in a if '/manuscript/' in k],'interpretation':'Observed endpoint differences only. No attribution of any change to historical checkpoints 72,73,74,75.'}
(OUT/'comparison_71_76.json').write_text(json.dumps(diff,indent=2)+'\n')
patch=[]
for k in changed:
    if k.endswith(('.lean','.md','.py','.toml')) or k.endswith('lean-toolchain'):
        p=ROOT/'restored/checkpoint_71'/k;q=ROOT/'restored/checkpoint_76'/k
        if max(p.stat().st_size,q.stat().st_size)>1000000:continue
        patch.extend(difflib.unified_diff(p.read_text().splitlines(True),q.read_text().splitlines(True),fromfile='checkpoint71/'+k,tofile='checkpoint76/'+k))
(OUT/'changed_text_files.diff').write_text(''.join(patch))
print(json.dumps({k:diff[k] for k in ['counts','active_lean_counts','active_lean_added','active_lean_changed','manuscripts']},indent=2))
