#!/usr/bin/env python3
"""Prepare pinned third-party dependencies, then run a fresh project compilation."""
from pathlib import Path
import argparse, datetime, json, os, shutil, signal, subprocess, sys
from verify_sources import ROOT, verify, verify_installed_pins
p=argparse.ArgumentParser()
p.add_argument('--skip-cache',action='store_true',help='Use an already prepared pinned third-party cache')
p.add_argument('--prepare-only',action='store_true')
p.add_argument('--audit-only',action='store_true',help='Check existing freshly built endpoints; does not claim a fresh build')
p.add_argument('--jobs',type=int,default=2)
p.add_argument('--module-timeout',type=int,default=180)
p.add_argument('--total-timeout',type=int,default=3600)
p.add_argument('--output',help='New result directory; defaults to a timestamp under run-results')
a=p.parse_args()
os.chdir(ROOT)
out=Path(a.output).resolve() if a.output else ROOT/'run-results'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
if out.exists() and any(out.iterdir()):raise SystemExit('Output directory must be new or empty')
out.mkdir(parents=True,exist_ok=True)
meta={'status':'PREPARING','phases':[],'output':str(out)}
env=dict(os.environ)
for k in ['LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LEAN_OPTS']:env.pop(k,None)
# Do not mutate the user's shell, Lean toolchain, or global configuration.
if shutil.which('lake') is None:raise SystemExit('lake not found: install elan or Lean 4.19.0, then retry')
def save(): (out/'run-summary.json').write_text(json.dumps(meta,indent=2)+'\n')
def run(label,cmd,timeout):
    with (out/(label+'.log')).open('w') as f:
        result=subprocess.Popen(cmd,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
        try:result.wait(timeout=timeout)
        except (subprocess.TimeoutExpired,KeyboardInterrupt):
            os.killpg(result.pid,signal.SIGTERM)
            try:result.wait(timeout=10)
            except subprocess.TimeoutExpired:os.killpg(result.pid,signal.SIGKILL);result.wait()
            raise
    meta['phases'].append({'phase':label,'command':cmd,'exit_code':result.returncode});save()
    if result.returncode:raise RuntimeError(f'{label} failed; see {out/(label+".log")}')
try:
    meta['source_check']=verify();save()
    run('lean-version',['lake','env','lean','--version'],600)
    if 'version 4.19.0,' not in (out/'lean-version.log').read_text():raise RuntimeError('Wrong Lean version')
    meta['installed_pins']=verify_installed_pins();save()
    if not a.skip_cache and not a.audit_only:
        run('third-party-cache',['lake','exe','cache','get'],1800)
    if a.prepare_only:
        meta['status']='DEPENDENCIES_PREPARED';save();raise SystemExit(0)
    cmd=['lake','env',sys.executable,'scripts/compile_sources.py','--output',str(out),
         '--jobs',str(a.jobs),'--module-timeout',str(a.module_timeout),'--total-timeout',str(a.total_timeout)]
    if a.audit_only:cmd.append('--audit-only')
    run('fresh-build' if not a.audit_only else 'endpoint-audit',cmd,a.total_timeout+2*a.module_timeout+120)
    meta['status']='PASS' if not a.audit_only else 'AUDIT_ONLY_PASS';save()
    print(f"{meta['status']}: {out}")
except (Exception,KeyboardInterrupt) as e:
    meta['status']='FAILED';meta['error']=str(e);save();print(str(e),file=sys.stderr);raise SystemExit(1)
