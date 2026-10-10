"""Track ONLY descendants of owned session leader; bounded exact cleanup."""
import os,signal,subprocess,time

def snapshot():
 raw=subprocess.check_output(['ps','-axo','pid=,ppid=,pgid=,lstart=,stat='],text=True,timeout=2)
 assert len(raw)<=2*1024**2,'bounded ps metadata'
 rows={}
 for line in raw.splitlines():
  parts=line.split()
  if len(parts)!=9:continue
  pid,ppid,pgid=map(int,parts[:3]);rows[pid]={'ppid':ppid,'pgid':pgid,'birth':' '.join(parts[3:8]),'state':parts[8]}
 return rows
class OwnedRunner:
 def __init__(self,proc):self.proc=proc;self.known={};self.groups={proc.pid};self.errors=[]
 def observe(self):
  rows=snapshot();pending=[self.proc.pid];seen=set()
  while pending:
   pid=pending.pop()
   if pid in seen or pid not in rows:continue
   if pid==self.proc.pid and ((pid in self.known and rows[pid]['birth']!=self.known[pid][0]) or (pid not in self.known and self.proc.poll() is not None)):continue
   seen.add(pid);row=rows[pid]
   if pid==self.proc.pid:
    assert row['pgid']==pid,'runner must own new session'
   elif row['pgid'] not in self.groups:
    # New group ownership only from a descendant group leader in this tree.
    assert row['pgid'] in rows and (row['pgid']==pid or row['pgid'] in seen),'unowned descendant process group'
   self.known[pid]=(row['birth'],row['pgid']);self.groups.add(row['pgid'])
   pending.extend(q for q,r in rows.items() if r['ppid']==pid)
  # Members of an already owned group may remain after leader reparent/reaping.
  for pid,row in rows.items():
   if row['pgid'] in self.groups and any(q in rows and rows[q]['birth']==birth and rows[q]['pgid']==pgid for q,(birth,pgid) in self.known.items() if pgid==row['pgid']):
    self.known[pid]=(row['birth'],row['pgid'])
  return rows
 def alive_groups(self,rows):
  return {pgid for pid,(birth,pgid) in self.known.items() if pid in rows and rows[pid]['birth']==birth and rows[pid]['pgid']==pgid and not rows[pid]['state'].startswith('Z')}
 def cleanup(self):
  report={'runner_pid':self.proc.pid,'signals':[],'errors':[],'owned_groups':[]};old={s:signal.getsignal(s) for s in [signal.SIGTERM,signal.SIGHUP,signal.SIGINT]}
  def send(group,sig):
   try:os.killpg(group,sig);report['signals'].append({'group':group,'signal':sig.name})
   except ProcessLookupError:pass
   except OSError as e:report['errors'].append(str(e))
  try:
   for sig in old:signal.signal(sig,signal.SIG_IGN)
   # Request graceful reviewed-runner cleanup BEFORE any ps call that might
   # fail. This runner owns its separately-sessioned Lean child directly.
   if self.proc.poll() is None:send(self.proc.pid,signal.SIGTERM)
   rows=self.observe()
   # Gracefully interrupt the reviewed runner first: it owns a separate Lean
   # session, so killing only runner's group would not clean that session.
   if self.proc.poll() is None:send(self.proc.pid,signal.SIGTERM)
   deadline=time.monotonic()+8
   while time.monotonic()<deadline:
    rows=self.observe();self.proc.poll()
    if self.proc.returncode is not None and not self.alive_groups(rows):break
    time.sleep(.1)
   rows=self.observe();groups=self.alive_groups(rows)
   if groups:
    # Freeze every observed OWNED group before a last descendant capture, so
    # fallback cleanup never intentionally leaves a forking owned runner.
    for group in sorted(groups):send(group,signal.SIGSTOP)
    rows=self.observe();groups=self.alive_groups(rows)
    for group in sorted(groups):send(group,signal.SIGKILL)
   self.proc.wait(timeout=5);rows=self.observe();remaining=self.alive_groups(rows)
   report.update(leader_reaped=self.proc.returncode is not None,runner_exit=self.proc.returncode,owned_groups=sorted(self.groups),remaining_owned_groups=sorted(remaining))
   assert not remaining,'owned descendant group survived cleanup'
  except BaseException as e:
   # Monitoring exceptions still kill only individually birth-qualified known
   # groups. No host-wide process-name kill is used.
   report['errors'].append(type(e).__name__+': '+str(e))
   try:
    if self.proc.poll() is None:
     send(self.proc.pid,signal.SIGTERM)
     try:self.proc.wait(timeout=8)
     except subprocess.TimeoutExpired:pass
    rows=snapshot()
    if self.proc.poll() is None:send(self.proc.pid,signal.SIGKILL)
    for group in sorted(self.alive_groups(rows)):send(group,signal.SIGKILL)
    self.proc.wait(timeout=5)
    report.update(leader_reaped=self.proc.returncode is not None,runner_exit=self.proc.returncode,owned_groups=sorted(self.groups),remaining_owned_groups=sorted(self.alive_groups(snapshot())))
   except BaseException as e:report['errors'].append(type(e).__name__+': '+str(e))
  finally:
   for sig,handler in old.items():signal.signal(sig,handler)
  return report
