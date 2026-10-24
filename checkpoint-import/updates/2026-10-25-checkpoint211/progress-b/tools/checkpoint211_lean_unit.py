"""Compile one local unit with the pinned Lean and exact manifest import paths.
The final Lake build remains a separate mandatory gate.
"""
from pathlib import Path
import json,os,subprocess,sys
P=Path(__file__).resolve().parents[1]
units=sys.argv[1:]
assert units and all(u.isidentifier() for u in units)
manifest=json.loads((P/'lake-manifest.json').read_text())
paths=[P/'.lake/packages'/v['name']/'.lake/build/lib/lean' for v in manifest['packages']]
paths.append(P/'.lake/build/lib/lean')
env=dict(os.environ);env['LEAN_PATH']=os.pathsep.join(map(str,paths))
for u in units:
 argv=['python3','tools/lean_command.py','lean','-R','.',
  '-o',f'.lake/build/lib/lean/PaperILean/{u}.olean',f'PaperILean/{u}.lean']
 print(json.dumps(dict(argv=argv,LEAN_PATH=env['LEAN_PATH'])),flush=True)
 r=subprocess.run(argv,cwd=P,env=env)
 print(f'{u}: exit {r.returncode}',flush=True)
 if r.returncode:raise SystemExit(r.returncode)
