"""Record actual commands and proof-source snapshots, including failed attempts."""
from pathlib import Path
import datetime,hashlib,json,subprocess,sys,fcntl
P=Path(__file__).resolve().parents[1];E=P/'evidence'
name,*argv=sys.argv[1:]
assert name and argv and all(c in 'abcdefghijklmnopqrstuvwxyz0123456789_' for c in name)
prefix='checkpoint_211_development' if name.startswith('dev_') else 'checkpoint_211'
lock=(E/(prefix+'_command_history.lock')).open('a');fcntl.flock(lock,fcntl.LOCK_EX)
history=E/(prefix+'_command_history.json')
data=json.loads(history.read_text()) if history.exists() else {'commands':[]}
n=len(data['commands'])+1;log=E/f'{prefix}_{n:03d}_{name}.log'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
hashes=lambda:{str(p.relative_to(P)):sha(p) for p in [P/'PaperILean.lean',*sorted((P/'PaperILean').glob('*.lean'))]}
start=datetime.datetime.now(datetime.timezone.utc).isoformat();before=hashes()
snapshot=E/(prefix+'_sources')/f'{n:03d}_{name}';snapshot.mkdir(parents=True)
for module in json.loads((P/'tools/checkpoint211_units.json').read_text()):
 p=P/'PaperILean'/f'{module}.lean'
 if p.exists():(snapshot/p.name).write_bytes(p.read_bytes())
with log.open('w') as stream:r=subprocess.run(argv,cwd=P,stdout=stream,stderr=subprocess.STDOUT)
after=hashes()
record=dict(name=name,argv=argv,cwd=str(P),start_utc=start,finish_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 exit_code=r.returncode,log=str(log.relative_to(P)),lean_source_sha256_before=before,lean_source_sha256=after,
 sources_unchanged_during_execution=before==after,source_snapshot=str(snapshot.relative_to(P)))
data['commands'].append(record);history.write_text(json.dumps(data,indent=2)+'\n')
print(f'{name}: exit {r.returncode}; {log.relative_to(P)}',flush=True)
if r.returncode:print(log.read_text()[-14000:])
raise SystemExit(r.returncode)


