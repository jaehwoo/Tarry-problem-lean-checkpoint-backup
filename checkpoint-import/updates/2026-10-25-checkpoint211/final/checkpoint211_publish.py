"""One-purpose upload to the existing private checkpoint backup repository."""
from pathlib import Path
import importlib.util,json,shutil,sys
ROOT=Path(__file__).resolve().parent
repo=Path.cwd();stage=repo/'checkpoint-import/updates/2026-10-25-checkpoint211/final'
transport=repo/'checkpoint-import/updates/2026-10-24-all-checkpoints/strict_github_transport.py'
spec=importlib.util.spec_from_file_location('strict211',transport);strict=importlib.util.module_from_spec(spec);spec.loader.exec_module(strict)
sys.path.insert(0,str(stage))
from checkpoint211_rehydrate import reconstruct,sha,jwrite
gh=Path(shutil.which('gh'));out=stage/'delivery';out.mkdir(exist_ok=True)
def api(endpoint,*args,**kwargs):return strict.api(endpoint,*args,gh=gh,**kwargs)
base='repos/jaehwoo/lean-checkpoint-backup';release=422682291
parent=out/'parent210.tar.zst'
metadata=api(base+'/releases/assets/672186419')
assert metadata['digest']=='sha256:e88baec2560feecf84093da841667201b8c67678bb31ce6aac3fd69eb34ab7be'
if not parent.exists():
 with parent.open('wb') as f:api(base+'/releases/assets/672186419','-H','Accept: application/octet-stream',output=f)
print('Exact parent archive downloaded; reconstructing full211 project.',flush=True)
reconstruct(stage,parent,out)
pages=api(base+f'/releases/{release}/assets?per_page=100','--paginate','--slurp')
existing={r['name']:r for page in pages for r in page}
files=sorted(p for p in out.glob('Paper_I_Lean_Checkpoint_211_*') if p.is_file())
checksums=out/'Paper_I_Lean_Checkpoint_211_SHA256SUMS.txt';checksums.write_bytes((out/'SHA256SUMS.txt').read_bytes());files.append(checksums)
saved=[]
for p in files:
 h=sha(p);r=existing.get(p.name)
 if r is None:
  r=api(f'https://uploads.github.com/{base}/releases/{release}/assets?name={p.name}',
        '--method','POST','-H','Content-Type: application/octet-stream','--input',str(p))
 assert r['digest']=='sha256:'+h and r['size']==p.stat().st_size,p.name
 # A fresh authenticated read through the repository's permitted CDN verifies bytes.
 fresh=out/('readback_'+p.name)
 with fresh.open('wb') as f:api(base+'/releases/assets/'+str(r['id']),'-H','Accept: application/octet-stream',output=f)
 assert sha(fresh)==h and fresh.stat().st_size==p.stat().st_size,p.name
 fresh.unlink()
 saved.append(dict(name=p.name,bytes=p.stat().st_size,sha256=h,asset_id=r['id'],url=r['browser_download_url'],fresh_download_verified=True))
 print('Saved and read back '+p.name,flush=True)
receipt=out/'Paper_I_Lean_Checkpoint_211_GitHub_Receipt.json'
jwrite(receipt,dict(checkpoint=211,repository='jaehwoo/lean-checkpoint-backup',release_id=release,
  all_artifacts_read_back=True,full_project_preserves_all_parent_members=True,assets=saved,
  proof_verification='Recorded local Lean4.19.0 runs; this workflow checks reconstruction, transfer and restore integrity only.',verification_complete=False))
r=existing.get(receipt.name)
if r is None:r=api(f'https://uploads.github.com/{base}/releases/{release}/assets?name={receipt.name}','--method','POST','-H','Content-Type: application/octet-stream','--input',str(receipt))
assert r['digest']=='sha256:'+sha(receipt)
print('Checkpoint211 GitHub backup complete: '+str(len(saved))+' verified artifacts.',flush=True)
