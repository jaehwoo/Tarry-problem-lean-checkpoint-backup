"""Check the exact pinned runtime, dependencies, and inherited protected sources."""
from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parents[1];W=P.parents[1]
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
b=json.loads((P/'evidence/checkpoint_211_baseline.json').read_text())
for f,h in b.items():
 if f!='PaperILean.lean':assert sha(P/f)==h,f
root=(P/'PaperILean.lean').read_bytes();added=b'\nimport PaperILean.OriginalCubicQuinticBoundary\n'
assert root.endswith(added) and hashlib.sha256(root[:-len(added)]).hexdigest()==b['PaperILean.lean']
packages=[]
for v in json.loads((P/'lake-manifest.json').read_text())['packages']:
 d=P/'.lake/packages'/v['name'];commit=subprocess.check_output(['git','-C',str(d),'rev-parse','HEAD'],text=True).strip()
 clean=not subprocess.check_output(['git','-C',str(d),'status','--porcelain','--untracked-files=no'],text=True)
 assert commit==v['rev'] and clean
 packages.append(dict(name=v['name'],commit=commit,tracked_source_clean=True))
c=W/'tmp/lean_continuation_runtime/lean-4.19.0-linux/bin/lean'
assert sha(c)=='92c3d35b5bfaa5e0fea413a775d504cf46cd95e1345df61c2274f76779e7e023'
for s in ['runtime','cache']:assert json.loads((P/f'evidence/checkpoint_211_restore_{s}.json').read_text())['passed']
record=dict(checkpoint=211,lean_version=subprocess.check_output(['python3','tools/lean_command.py','lean','--version'],cwd=P,text=True).strip(),compiler_sha256=sha(c),packages=packages,unchanged_protected_entries=len(b)-1,root_only_added_import=True,manuscripts={str(p.relative_to(P)):sha(p) for p in (P/'manuscript').glob('*.tex')},original_route_retained=True,native_evaluation_used=False,recovery='Exact saved210 source, official pinned compiler, nine pinned Git bundles, byte-checked base125 cache and210 overlay. Inactive inherited transfer copies remain unchanged in the parent archive; see archived-copy receipt. Proof gates were freshly executed after restoration.')
(P/'evidence/checkpoint_211_environment.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
