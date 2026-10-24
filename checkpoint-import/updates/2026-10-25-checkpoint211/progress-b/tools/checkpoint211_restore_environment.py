"""Restore the saved pinned environment after automated workspace pruning."""
from pathlib import Path
import hashlib,json,subprocess,sys,zipfile,shutil,datetime
P=Path(__file__).resolve().parents[1];W=P.parents[1];D=W/'downloads/Tarry';R=W/'tmp/lean_continuation_runtime'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
commands=[]
def run(argv):
 print(json.dumps(argv),flush=True);r=subprocess.run(argv,cwd=P);commands.append(dict(argv=argv,exit_code=r.returncode));assert r.returncode==0
stage=sys.argv[1]
if stage=='runtime':
 assert sha(D/'Lean_4.19.0_Linux_Recovery.tar.zst')=='6fe3ce97a58f44e2b3567d455b994eacec5bfe9ae7774f2a573444480ba813fe'
 R.mkdir(parents=True,exist_ok=True)
 run(['tar','--no-same-owner','--zstd','-xf',str(D/'Lean_4.19.0_Linux_Recovery.tar.zst'),'-C',str(R)])
 run(['gcc','-shared','-fPIC','-o',str(R/'own_exe.so'),str(P/'tools/own_exe.c'),'-ldl'])
 kit=W/'source_kit'
 with zipfile.ZipFile(D/'Paper_I_Lean_Checkpoint_125_Pinned_Dependencies.zip') as z:
  assert z.testzip() is None
  assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in z.namelist());z.extractall(kit)
 run(['python3','tools/checkpoint125_restore_sources.py',str(kit),str(P/'.lake/packages')])
 run(['python3','tools/lean_command.py','lean','--version'])
 assert sha(R/'lean-4.19.0-linux/bin/lean')=='92c3d35b5bfaa5e0fea413a775d504cf46cd95e1345df61c2274f76779e7e023'
elif stage=='cache':
 spec=json.loads((P/'tools/Checkpoint125_CacheParts.json').read_text());out=Path('/tmp/checkpoint211_base125.tar.zst');assert not out.exists()
 with out.open('wb') as dst:
  for r in spec['parts']:
   p=D/r['filename'];assert sha(p)==r['zip_sha256']
   with zipfile.ZipFile(p) as z:
    assert z.namelist()==[r['entry']]
    h=hashlib.sha256();n=0
    with z.open(r['entry']) as src:
     while b:=src.read(8<<20):dst.write(b);h.update(b);n+=len(b)
    assert n==r['size_bytes'] and h.hexdigest()==r['sha256']
 assert out.stat().st_size==spec['archive_size_bytes'] and sha(out)==spec['archive_sha256']
 run(['tar','--no-same-owner','--zstd','-xf',str(out),'-C',str(P)])
 manifest=json.loads((P/'cache_manifest.json').read_text());assert len(manifest['files'])==46640
 for r in manifest['files']:
  p=P/r['path'];assert p.stat().st_size==r['size_bytes'] and sha(p)==r['sha256'],r['path']
 cache=D/'Paper_I_Lean_Checkpoint_210_Compiled_Project_Cache.tar.zst'
 assert sha(cache)=='c2ad35ef75ab729d997b8fe8f44c50845f86246e1ec39ce5968690ca6517adf3'
 run(['tar','--no-same-owner','--zstd','-xf',str(cache),'-C',str(P)])
 manifest=json.loads((P/'evidence/checkpoint_210_project_cache_manifest.json').read_text())
 for r in manifest['files']:
  p=P/r['path'];assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],r['path']
else:raise ValueError(stage)
record=dict(stage=stage,passed=True,commands=commands,finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),source='Saved compiler, nine exact git bundles, base125 compiled cache and210 project/cache delta (210); no pin changes.',proof_verification_claim=False)
(P/f'evidence/checkpoint_211_restore_{stage}.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
