"""Bounded, monitored DATA seal; no proof process is launched."""
import hashlib,json,os,re,shutil,signal,subprocess,sys,time
from pathlib import Path
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-transfer-cut12'
log=O/'seal-guard01.log';receipt=O/'seal-guard01.json';assert not log.exists() and not receipt.exists()
command=[sys.executable,'-I','-B','-S',str(S/'seal_packet.py')]
started=time.monotonic();peak=0;minimum_memory=100;minimum_disk=shutil.disk_usage(S).free
with log.open('w') as output:
 proc=subprocess.Popen(command,cwd=R,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
 reason=None
 while proc.poll() is None:
  memory=int(re.search(r'System-wide memory free percentage: (\d+)%',subprocess.check_output(['memory_pressure'],text=True)).group(1))
  processlist=subprocess.check_output(['ps','-axo','pgid=,rss='],text=True)
  rss=sum(int(line.split()[1])*1024 for line in processlist.splitlines() if len(line.split())==2 and int(line.split()[0])==proc.pid)
  disk=shutil.disk_usage(S).free;peak=max(peak,rss);minimum_memory=min(minimum_memory,memory);minimum_disk=min(minimum_disk,disk)
  if time.monotonic()-started>240:reason='DATA seal timeout'
  elif rss>1024**3:reason='DATA seal1GiB RSS guard'
  elif memory<15:reason='memory admission'
  elif disk<2*1024**3:reason='disk admission'
  if reason:
   os.killpg(proc.pid,signal.SIGTERM)
   try:proc.wait(timeout=5)
   except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
   break
  time.sleep(.5)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
result=dict(status='passed' if proc.returncode==0 and not reason else 'failed',command=command,exit=proc.returncode,reason=reason,seconds=time.monotonic()-started,peak_group_rss_bytes=peak,minimum_memory_free_percent=minimum_memory,minimum_disk_free_bytes=minimum_disk,log_sha256=sha(log),guard_sha256=sha(Path(__file__)),seal_recipe_sha256=sha(S/'seal_packet.py'),scope='DATA byte seal only, zero additional kernel runs')
receipt.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result));sys.exit(0 if result['status']=='passed' else 1)
