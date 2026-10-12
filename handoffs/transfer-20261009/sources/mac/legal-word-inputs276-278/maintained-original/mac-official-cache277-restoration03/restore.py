from pathlib import Path,PurePosixPath
import sys,os,json,hashlib,runpy,signal,subprocess,time,struct,compression.zstd as z
S=Path(__file__).resolve().parent;W=S.parent;A=W/'mac-official-cache277-restoration01';G=W/'mac-full-arithmetic45-execution303/maintained/guard.py';P=A/'plan01.json';TERMS={signal.SIGINT,signal.SIGTERM,signal.SIGHUP};CANCEL=False
def require(v,m):
 if not v:raise RuntimeError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def read(v):
 p=Path(v['path']);require(p.is_file()and not p.is_symlink()and p.stat().st_size==v['bytes'],'ordinary exact input');raw=p.read_bytes();require(hashlib.sha256(raw).hexdigest()==v['sha256'],'input SHA');return raw
def put(p,v):
 with p.open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n');f.flush();os.fsync(f.fileno())
 fd=os.open(p.parent,os.O_RDONLY);os.fsync(fd);os.close(fd)
def cancel(*args):
 global CANCEL
 CANCEL=True
def framed(raw,dictionary):
 require(raw[:4]==b'LTR3'and len(raw)<=4*1024**2,'exact bounded LTR3');pos=12;capacity=0;names=[]
 def take(n):
  nonlocal pos
  require(n>=0 and pos+n<=len(raw),'closed framing');out=raw[pos:pos+n];pos+=n;return out
 def string():
  end=raw.find(b'\0',pos);require(end>=pos and end-pos<=1024,'bounded path');b=take(end-pos);take(1);return b.decode()
 def path(indexed=True):
  if indexed:require(take(1)==b'\0','single root')
  v=string()
  if v:require(v.startswith('./.lake/build/')and not PurePosixPath(v).is_absolute()and '..'not in PurePosixPath(v).parts,'confined output');names.append(v)
  return v
 def payload():
  nonlocal capacity
  code=take(1)[0]
  if code==5:path();path()
  if code in[0,1,5]:
   b=take(struct.unpack('<Q',take(8))[0])
   if code==0:
    d=z.ZstdDecompressor();body=d.decompress(b,max_length=16*1024**2+1);require(d.eof and not d.unused_data and len(body)<=16*1024**2,'bounded ordinary Zstd EOF');capacity+=len(body)
   else:
    prefix=z.ZstdDecompressor(zstd_dict=dictionary).decompress(b,max_length=16);require(len(prefix)==16,'LGZ prefix');size=struct.unpack('<Q',prefix[8:])[0];require(size<=16*1024**2,'LGZ bound');capacity+=size+3*65536
  elif code in[2,3]:take(8);capacity+=1024
  elif code==4:
   take(32)
   while True:
    tag=take(1)[0]
    if tag==0:break
    require(tag in[1,2],'trace hash tag');take(8)
   capacity+=4096
  else:raise RuntimeError('unknown compression code')
 path(False);payload()
 while pos<len(raw):
  if path():payload()
  else:string()
 require(pos==len(raw)and len(names)==len(set(names)),'exact complete output framing/keyset');return capacity,names
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated supported interpreter');require(not (signal.pthread_sigmask(signal.SIG_BLOCK,set())&TERMS),'unblocked parent signals')
for sig in TERMS:signal.signal(sig,cancel)
require(pin(P)['sha256']=='aed8a7d8c53580dc7c8162522ff467d6833e459e8fcc50e75bca89cfa0436fed','frozen restoration plan');plan=json.loads(P.read_bytes());require(plan['schema']=='exact-official-cache-restoration277'and len(plan['records'])==627,'closed required cache');read(plan['tool']);read(plan['old_official_manifest']);read(plan['current_official_manifest']);dictionary=z.ZstdDict(read(plan['dictionary']));require(pin(G)['sha256']=='888bb69348a545de15a4e1a2eba2b62ca422289e7cc19d7bbc156c9293957567','reviewed ownership/resource helpers');g=runpy.run_path(str(G),run_name='RESTORATION_OWNERSHIP_ONLY')
table=g['processes']();require(not any(Path(p['comm']).name in{'lean','lake','cargo','rustc','leantar'}for p in table.values()),'idle heavy verifier/cache lane');require(not any('dispatcher/serial.py --max-jobs' in v for v in subprocess.check_output(['/bin/ps','-axo','command='],timeout=5).decode().splitlines()),'no live dispatcher');free=os.statvfs(W).f_bavail*os.statvfs(W).f_frsize;require(free>=2*1024**3+2*max(v['capacity_bound']for v in plan['records'])+1048576 and g['free_memory']()>=15,'largest single transaction reserve plus unchanged physical floor');runtime=S/'runtime';require(not runtime.exists(),'exclusive no reset');runtime.mkdir();completed=[]
for index,item in enumerate(plan['records']):
 require(not CANCEL,'cancellation before cache transaction');require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=2*1024**3+2*item['capacity_bound']+1048576 and g['free_memory']()>=15,'fresh current transaction reserve');raw=read(item['archive']);read(item['source']);capacity,names=framed(raw,dictionary);require(capacity==item['capacity_bound'],'exact capacity plan');scratch=runtime/('scratch-'+str(index).zfill(4));scratch.mkdir();copied=scratch/'input.ltar';copied.write_bytes(raw);require(pin(copied)['sha256']==item['archive']['sha256'],'exact disposable archive copy');stdout=runtime/('extract-'+str(index).zfill(4)+'.stdout');stderr=runtime/('extract-'+str(index).zfill(4)+'.stderr');proc=None;birth='';seen={};peak=0;error=None;cleanup=None;start=time.monotonic();command=[plan['tool']['path'],'-x','--jobs','1','-C',str(scratch),str(copied)];mask=signal.pthread_sigmask(signal.SIG_BLOCK,TERMS)
 try:
  require(not CANCEL,'cancelled critical startup')
  with stdout.open('xb')as so,stderr.open('xb')as se:
   def unmask():signal.pthread_sigmask(signal.SIG_SETMASK,mask)
   proc=subprocess.Popen(command,env={'HOME':'/Users/antoinecyr','LANG':'C','PATH':'/usr/bin:/bin','LEAN_NUM_THREADS':'1'},stdin=subprocess.DEVNULL,stdout=so,stderr=se,start_new_session=True,preexec_fn=unmask)
   table=g['processes']()
   if proc.pid in table:birth=table[proc.pid]['birth'];seen[proc.pid]=birth
   signal.pthread_sigmask(signal.SIG_SETMASK,mask)
   last=0
   while proc.poll()is None:
    elapsed=time.monotonic()-start;require(not CANCEL and elapsed<=240,'bounded cancellation-aware extraction');table=g['processes']();owned=g['owned'](table,proc,birth,seen);rss=sum(v['rss']for v in owned.values());peak=max(peak,rss);require(rss<=4*1024**3,'owned extraction RSS');require(stdout.stat().st_size<=65536 and stderr.stat().st_size<=65536,'bounded extraction streams')
    if elapsed-last>=1:require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=2*1024**3 and g['free_memory']()>=15,'live physical RAM/disk');last=elapsed
    time.sleep(.05)
 except BaseException as e:error=repr(e)
 finally:
  signal.pthread_sigmask(signal.SIG_BLOCK,TERMS)
  if proc is not None:cleanup=g['cleanup'](proc,birth,seen)
  signal.pthread_sigmask(signal.SIG_SETMASK,mask)
 require(proc is not None and type(proc.returncode)is int and proc.returncode==0 and error is None and cleanup['clean']and cleanup['leader_reaped'],'typed extraction/cleanup success');require(stdout.stat().st_size<=65536 and stderr.stat().st_size<=65536 and stderr.read_bytes()==b'','strict extraction diagnostics');outputs={};temporary={}
 for path in scratch.rglob('*'):
  require(not path.is_symlink(),'no extracted symlink')
  if path.is_file():temporary[str(path)]=pin(path)
 require(sum(v['bytes']for v in temporary.values())<=capacity+len(raw),'actual scratch capacity bound');prefix=scratch/'.lake/build/lib/lean';relative=Path(item['module'].replace('.','/'))
 require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=2*1024**3+sum((prefix/Path(str(relative)+suffix)).stat().st_size for suffix,v in item['wanted'].items()if v['sha256']is not None)+1048576,'install reserve with original floor')
 for suffix,wanted in item['wanted'].items():
  source=prefix/Path(str(relative)+suffix);target=Path(wanted['path'])
  if wanted['sha256']is None:
   require(not target.exists()and not target.is_symlink(),'unselected companion stays absent');continue # original manifest did not include IR; extra scratch IR is recorded/discarded, never installed
  require(source.is_file()and not source.is_symlink(),'exact required companion');v=pin(source);require(v['sha256']==wanted['sha256'],'original official SHA');require(not target.is_symlink(),'ordinary official cache target')
  if target.exists():
   require(target.is_file()and pin(target)['sha256']==wanted['sha256'],'only exact original partial installed output');outputs[str(target)]=pin(target);continue
  target.parent.mkdir(parents=True,exist_ok=True)
  with target.open('xb')as f:f.write(source.read_bytes());f.flush();os.fsync(f.fileno())
  outputs[str(target)]=pin(target);require(outputs[str(target)]['sha256']==wanted['sha256'],'installed exact SHA')
 put(runtime/('restored-'+str(index).zfill(4)+'.json'),dict(module=item['module'],input_archive=item['archive'],source=item['source'],command=command,exit=proc.returncode,elapsed=time.monotonic()-start,peak_group_rss=peak,cleanup=cleanup,objects=outputs,disposable_scratch=temporary,scope='Exact official cache restoration; no Lean compiler invocation or new qualification.'))
 # Only own scratch replicas of recorded outputs/input are discarded after durable original mapping.
 for path in sorted(scratch.rglob('*'),key=lambda p:len(p.parts),reverse=True):
  if path.is_file():require(pin(path)==temporary[str(path)],'scratch unchanged before discard');path.unlink()
  elif path.is_dir():path.rmdir()
 scratch.rmdir();completed.append(dict(module=item['module'],objects=outputs));require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=2*1024**3,'terminal physical floor')
 if (index+1)%20==0:print(json.dumps(dict(restored=index+1,objects=sum(len(v['objects'])for v in completed),free=os.statvfs(W).f_bavail*os.statvfs(W).f_frsize)),flush=True)
put(S/'result01.json',dict(status='EXACT_OFFICIAL_CACHE_RESTORED_NO_LEAN',modules=len(completed),records=completed,physical_restored_bytes=sum(v['bytes']for r in completed for v in r['objects'].values()),old_manifest=plan['old_official_manifest'],free_disk=os.statvfs(W).f_bavail*os.statvfs(W).f_frsize));print(json.dumps(dict(result=pin(S/'result01.json'),modules=len(completed),free=os.statvfs(W).f_bavail*os.statvfs(W).f_frsize)))
