"""Actual runner prelaunch boundary: observations outside gated state, no spawning."""
import fcntl,hashlib,json,os,time
from pathlib import Path
from admission_gate import exclusive_write
class ObservationArea:
 def __init__(self,directory,max_records=64,max_total_bytes=4*1024**2):
  self.directory=Path(directory);self.max_records=max_records;self.max_total_bytes=max_total_bytes
 def write(self,result):
  d=self.directory;assert d.is_dir() and not d.is_symlink(),'fixed observation area missing'
  lock=d/'observations.lock';assert lock.is_file() and not lock.is_symlink()
  descriptor=os.open(lock,os.O_RDWR|os.O_NOFOLLOW);owned=False
  try:
   deadline=time.monotonic()+2
   while not owned:
    try:fcntl.flock(descriptor,fcntl.LOCK_EX|fcntl.LOCK_NB);owned=True
    except BlockingIOError:
     if time.monotonic()>deadline:raise RuntimeError('finite observation lock refusal')
     time.sleep(.02)
   records=list(d.glob('observation-*.json'));assert all(p.is_file() and not p.is_symlink() for p in records)
   assert len(records)<self.max_records,'bounded preflight observation count'
   classification=('POST-CLAIM incomplete transition; consumed/uncertain state requires explicit reconciliation; NOT zero-intent' if result.get('claim_transition_started') else 'ZERO-INTENT preflight/refusal observation; not a launched build receipt')
   payload=(json.dumps(dict(result,fresh_credit=0,classification=classification),indent=2)+'\n').encode()
   assert sum(p.stat().st_size for p in records)+len(payload)<=self.max_total_bytes,'bounded preflight observation bytes'
   path=d/('observation-'+str(time.time_ns())+'.json');exclusive_write(path,payload);return path
  finally:
   if owned:fcntl.flock(descriptor,fcntl.LOCK_UN)
   os.close(descriptor)
class Boundary:
 def __init__(self,gate,area):self.gate=gate;self.area=area;self.refusal_observed=False
 def prepare(self,admission_validation,source_import_preflight,volatile_preflight,admission,admission_sha256,module):
  try:
   admission_validation();source_import_preflight();volatile_preflight()
   self.gate.authorize(admission,admission_sha256,module)
   # Immediately before begin(), repeat live process/RAM/disk/byte checks
   # under the successfully owned lock. No claim/receipt/intent exists yet.
   source_import_preflight()
   volatile_preflight()
   return True
  except BaseException as error:
   try:self.area.write({'module':module,'reason':str(error),'error_type':type(error).__name__,'admission_sha256':admission_sha256});self.refusal_observed=True
   finally:self.gate.release()
   raise
