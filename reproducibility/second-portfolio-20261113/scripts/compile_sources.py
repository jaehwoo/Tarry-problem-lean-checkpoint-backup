#!/usr/bin/env python3
"""Fresh, bounded compilation of the frozen first-party import closure.
Run through `lake env python3`; no historical project .olean is used.
"""
from pathlib import Path
import argparse, concurrent.futures, datetime, hashlib, json, os, signal
import shutil, subprocess, sys, time
from verify_sources import ROOT, verify, verify_installed_pins

p=argparse.ArgumentParser()
p.add_argument('--output',required=True)
p.add_argument('--jobs',type=int,default=2)
p.add_argument('--module-timeout',type=int,default=180)
p.add_argument('--total-timeout',type=int,default=3600)
p.add_argument('--audit-only',action='store_true')
a=p.parse_args()
if not 1<=a.jobs<=8:raise SystemExit('--jobs must be between 1 and 8')
out=Path(a.output).resolve();out.mkdir(parents=True,exist_ok=True)
manifest=json.loads((ROOT/'provenance/source-manifest.json').read_text())
summary={'status':'RUNNING','fresh_first_party':not a.audit_only,'started_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'source_preflight':verify(),'installed_pins':verify_installed_pins(),'workers_per_lean_process':1,
         'parallel_modules':a.jobs,'module_timeout_seconds':a.module_timeout,'total_timeout_seconds':a.total_timeout,
         'default_maxHeartbeats':200000,'default_maxRecDepth':512,'records':[],'blocked_modules':[]}
started=time.monotonic();build=ROOT/'.lake/build/lib/lean';active={}

def stop_signal(signum, frame):
    for proc in list(active.values()):
        try:os.killpg(proc.pid,signal.SIGKILL)
        except ProcessLookupError:pass
    raise KeyboardInterrupt

signal.signal(signal.SIGTERM,stop_signal)
signal.signal(signal.SIGINT,stop_signal)

def save():
    summary['elapsed_seconds']=round(time.monotonic()-started,3)
    tmp=out/'build-summary.json.tmp';tmp.write_text(json.dumps(summary,indent=2)+'\n');tmp.replace(out/'build-summary.json')

def compile_one(module,relative,timeout):
    log=out/(module+'.log');dest=build/Path(module.replace('.','/'))
    dest.parent.mkdir(parents=True,exist_ok=True)
    command=['lean','-j1','-DmaxHeartbeats=200000','-DmaxRecDepth=512',
             '-o',str(dest.relative_to(ROOT))+'.olean','-i',str(dest.relative_to(ROOT))+'.ilean',relative]
    t=time.monotonic();timed_out=False
    with log.open('w') as f:
        proc=subprocess.Popen(command,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
        active[module]=proc
        try:code=proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out=True;os.killpg(proc.pid,signal.SIGKILL);proc.wait();code=124
        finally:active.pop(module,None)
    content=log.read_text(errors='replace')
    # Compiler warnings must not silently certify admitted proof bodies.
    if "declaration uses 'sorry'" in content or 'sorryAx' in content:code=65
    products={}
    if code==0:
        for ext in ['.olean','.ilean']:
            f=Path(str(dest)+ext)
            if not f.is_file():code=66;break
            products[str(f.relative_to(ROOT))]=hashlib.sha256(f.read_bytes()).hexdigest()
    return {'module':module,'command':command,'exit_code':code,'timed_out':timed_out,
            'seconds':round(time.monotonic()-t,3),'log':log.name,
            'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'products':products}

try:
    # Only generated first-party products are removed. The dependency cache remains.
    if not a.audit_only:
        for name in ['PaperILean','Repro']:
            target=build/name
            if target.is_symlink():raise RuntimeError(f'Refusing symlink build directory {target}')
            if target.exists():shutil.rmtree(target)
        pending=set(manifest['sources']);done=set();failed=set();running={}
        deps={n:{x for x in manifest['imports'][n] if x.startswith('PaperILean.')} for n in pending}
        with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
            while pending or running:
                if time.monotonic()-started>a.total_timeout:raise TimeoutError('Overall compilation time limit reached')
                for n in manifest['topological_order']:
                    if n not in pending:continue
                    if deps[n]&failed:
                        pending.remove(n);failed.add(n);summary['blocked_modules'].append({'module':n,'failed_dependencies':sorted(deps[n]&failed)})
                    elif deps[n]<=done and len(running)<a.jobs:
                        pending.remove(n);running[pool.submit(compile_one,n,manifest['sources'][n]['path'],min(a.module_timeout,max(1,a.total_timeout-(time.monotonic()-started))))]=n
                if not running:
                    if pending:raise RuntimeError('No schedulable module; incomplete dependency closure')
                    break
                finished,_=concurrent.futures.wait(running,timeout=1,return_when=concurrent.futures.FIRST_COMPLETED)
                for f in finished:
                    n=running.pop(f);r=f.result();summary['records'].append(r)
                    (done if r['exit_code']==0 else failed).add(n)
                    if r['exit_code'] or len(done)%25==0:print(f"compiled={len(done)} failed_or_blocked={len(failed)} remaining={len(pending)+len(running)} latest={n} code={r['exit_code']}",flush=True)
                    save()
        summary['compiled_modules']=len(done)
        summary['failed_modules']=[r['module'] for r in summary['records'] if r['exit_code']]
        if failed:
            summary['status']='BUILD_FAILED';save();raise SystemExit(1)
    for module in ['Repro.Endpoints','Repro.AuditEndpoints']:
        r=compile_one(module,module.replace('.','/')+'.lean',a.module_timeout)
        summary['records'].append(r);save()
        if r['exit_code']:
            summary['status']='ENDPOINT_CHECK_FAILED';save();raise SystemExit(1)
    audit=(out/'Repro.AuditEndpoints.log').read_text()
    if audit.count('ENDPOINT_AUDIT_PASS')!=4:raise RuntimeError('Expected four endpoint audit pass records')
    summary['status']='PASS' if not a.audit_only else 'AUDIT_ONLY_PASS'
    summary['endpoint_audit_pass_count']=4
    print(summary['status'],flush=True)
except (Exception,KeyboardInterrupt) as e:
    summary['status']='INTERRUPTED' if isinstance(e,KeyboardInterrupt) else 'RUNNER_ERROR'
    summary['error']=repr(e)
    for proc in list(active.values()):
        try:os.killpg(proc.pid,signal.SIGKILL)
        except ProcessLookupError:pass
    save();raise
finally:save()
