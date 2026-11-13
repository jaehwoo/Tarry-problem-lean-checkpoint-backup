"""Bound one owned subprocess group at 180s with cleanup ending by 185s.

This controls wall time only. It changes neither Lean heartbeats/recursion nor
proof auditing. Nested runner calls inherit the owning group's watchdog.
"""
import os,signal,subprocess,time
MARKER='AFFINE_BATCH_WATCHDOG_ACTIVE'
WALL_SECONDS=180
OUTER_SECONDS=185

def run(args,*,cwd=None,env=None,stdout=None,stderr=None,text=False,capture_output=False):
    """subprocess.run-like result, plus timed_out and owned_group metadata."""
    if capture_output:
        if stdout is not None or stderr is not None:raise ValueError('capture_output conflicts with output streams')
        stdout=stderr=subprocess.PIPE
    effective=os.environ.copy() if env is None else dict(env)
    effective[MARKER]='1'
    start=time.monotonic();timed_out=False
    proc=subprocess.Popen(args,cwd=cwd,env=effective,stdout=stdout,stderr=stderr,text=text,start_new_session=True)
    group=proc.pid
    assert os.getpgid(proc.pid)==group
    try:
        out,err=proc.communicate(timeout=WALL_SECONDS)
        returncode=proc.returncode
    except subprocess.TimeoutExpired:
        timed_out=True
        try:os.killpg(group,signal.SIGTERM)
        except ProcessLookupError:pass
        try:
            out,err=proc.communicate(timeout=max(0.0,OUTER_SECONDS-(time.monotonic()-start)))
        except subprocess.TimeoutExpired:
            out=err=None
        finally:
            # Kill this owned group even if its wrapper already exited.
            try:os.killpg(group,signal.SIGKILL)
            except ProcessLookupError:pass
            out2,err2=proc.communicate()
            if out2 is not None:out=out2
            if err2 is not None:err=err2
        returncode=124
    result=subprocess.CompletedProcess(args,returncode,out,err)
    result.timed_out=timed_out;result.owned_process_group=group
    result.wall_timeout_seconds=WALL_SECONDS;result.outer_timeout_seconds=OUTER_SECONDS
    result.seconds=time.monotonic()-start
    return result

def metadata(result):
    return {'timed_out':result.timed_out,'owned_process_group':result.owned_process_group,
            'wall_timeout_seconds':result.wall_timeout_seconds,'outer_timeout_seconds':result.outer_timeout_seconds}
