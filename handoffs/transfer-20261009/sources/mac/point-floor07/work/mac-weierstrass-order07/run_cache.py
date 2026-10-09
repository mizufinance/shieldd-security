import hashlib,json,os,re,shutil,signal,subprocess,time,sys
from pathlib import Path
S=Path(__file__).resolve().parent;R=S.parents[1];P=S/'project';O=R/'outputs/mac-weierstrass-order07';h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=P/'.lake/packages/mathlib/Cache/Main.lean';identity=h(source)
command=['lake','env','lean','-j1','-M2048','--run',str(source),'get','Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point','Mathlib.GroupTheory.OrderOfElement'];attempt=1
while (O/f'cache-guard{attempt:02d}.json').exists():attempt+=1
receipt=O/f'cache-guard{attempt:02d}.json';log=receipt.with_suffix('.log');start=time.monotonic();peak=0;reason=None;env=dict(os.environ,LEAN_NUM_THREADS='1')
with log.open('w') as output:
 process=subprocess.Popen(command,cwd=P,stdout=output,stderr=subprocess.STDOUT,start_new_session=True,env=env)
 while process.poll() is None:
  text=subprocess.check_output(['ps','-axo','pgid=,rss='],text=True);rss=sum(int(v[1])*1024 for line in text.splitlines() if len(v:=line.split())==2 and int(v[0])==process.pid);peak=max(peak,rss)
  free=int(re.search(r'System-wide memory free percentage: (\d+)%',subprocess.check_output(['memory_pressure'],text=True)).group(1))
  if time.monotonic()-start>240:reason='time bound'
  elif rss>4*1024**3:reason='RSS bound'
  elif free<15:reason='memory pressure'
  elif shutil.disk_usage(R).free<2*1024**3:reason='disk bound'
  if reason:
   os.killpg(process.pid,signal.SIGTERM)
   try:process.wait(timeout=5)
   except subprocess.TimeoutExpired:os.killpg(process.pid,signal.SIGKILL);process.wait()
   break
  time.sleep(.5)
result=dict(status='passed' if process.returncode==0 and h(source)==identity else 'failed',exit=process.returncode,command=command,source_sha256=identity,source_after_equal=True if h(source)==identity else False,seconds=time.monotonic()-start,peak_group_rss_bytes=peak,reason=reason,log_sha256=h(log),proof_credit=0,scope='exact pinned official cache retrieval in isolated package copy only')
receipt.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result));sys.exit(0 if result['status']=='passed' else 1)
