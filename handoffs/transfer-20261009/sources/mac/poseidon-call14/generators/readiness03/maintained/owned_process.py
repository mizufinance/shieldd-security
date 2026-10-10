"""Bounded cleanup of exactly a subprocess created with start_new_session=True."""
import os,signal,subprocess,time

def cleanup_owned(proc,grace_seconds=5):
    # The caller owns this session/process group; no host-wide process matching.
    assert 0 < grace_seconds <= 5
    observation={'process_group':proc.pid,'signals':[],'errors':[],'leader_exit_before':proc.poll()}
    def send(sig):
        try:os.killpg(proc.pid,sig);observation['signals'].append(sig.name)
        except ProcessLookupError:pass
        except OSError as error:observation['errors'].append(type(error).__name__+': '+str(error))
    def exists():
        # macOS can refuse killpg(pgid,0) after a group disappears. Observe only
        # this exact owned pgid; zombies cannot continue executing work.
        try:
            text=subprocess.check_output(['ps','-axo','pgid=,stat='],text=True,timeout=2)
            return any(len(p:=line.split())==2 and int(p[0])==proc.pid and not p[1].startswith('Z') for line in text.splitlines())
        except (OSError,subprocess.SubprocessError) as error:
            observation['errors'].append(type(error).__name__+': '+str(error));return True
    # Terminate residual children even if the original leader already exited.
    if exists():send(signal.SIGTERM)
    deadline=time.monotonic()+grace_seconds
    while exists() and time.monotonic()<deadline:
        proc.poll();time.sleep(.05)
    if exists():send(signal.SIGKILL)
    try:proc.wait(timeout=5)
    except (subprocess.TimeoutExpired,OSError) as error:
        observation['errors'].append(type(error).__name__+': '+str(error))
        send(signal.SIGKILL)
        try:proc.wait(timeout=5)
        except (subprocess.TimeoutExpired,OSError) as again:
            observation['errors'].append(type(again).__name__+': '+str(again))
    observation['leader_exit_after']=proc.poll()
    observation['leader_reaped']=proc.returncode is not None
    return observation
