from pathlib import Path
import json,hashlib,lzma,os,sys,runpy,subprocess,re,stat,signal
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=Path(__file__).resolve().parent;P=W/'mac-full-arithmetic45-execution302';CANCELLED=False
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(p,v):
 with p.open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n');f.flush();os.fsync(f.fileno())
 fd=os.open(p.parent,os.O_RDONLY);os.fsync(fd);os.close(fd)
def cancel(signum,frame):
 global CANCELLED
 CANCELLED=True
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated preservation')
for term in [signal.SIGTERM,signal.SIGHUP,signal.SIGINT]:signal.signal(term,cancel)
raw=subprocess.check_output(['/bin/ps','-axo','pid=,command='],text=True,timeout=5);require(not any(re.search(r'(?:/bin/lean |mac-full-arithmetic45-execution[0-9]+/dispatcher/serial.py --max-jobs)',line)for line in raw.splitlines()),'idle verifier lane')
require(not(S/'archives').exists()and not(S/'aliases-manifest01.json').exists(),'exclusive one-shot preservation')
g=runpy.run_path(str(P/'maintained/guard.py'),run_name='SOURCE_IDENTITY');g['require'](pin(P/'maintained/guard.py')['sha256']=='77e05e4eb1caeb76f58bf3dbfd45ebd7107391ac26b8ef2b464842c6d4e96b21','exact prior guard');cfg=g['read_config'](str(P/'config01.json'),pin(P/'config01.json')['sha256']);roots=[];seen={};g['carried_check'](cfg);g['checked_phase_close']()
for ordinal in range(1,302):
 root=W/('mac-full-arithmetic45-execution'+str(ordinal));directory=root/'own-cache/ShielddSecurity'
 if not directory.is_dir():continue
 links={p.name:p for p in directory.iterdir()if p.is_symlink()}
 if not links:continue
 producer=json.loads((root/'producer-manifest01.json').read_bytes());overlay=producer['overlay-manifest01.json'];layout=g['strict_json'](g['read_pin'](overlay));expected=layout['aliases'];require(set(expected)=={str(p)for p in links.values()},'exact inactive alias keyset')
 data={}
 for name,path in links.items():
  require(not CANCELLED,'cancellation before mutation');v=expected[str(path)];require(os.readlink(path)==v['path'],'absolute original input alias');g['checked_pin'](v);st=path.lstat();require(stat.S_ISLNK(st.st_mode)and st.st_size==len(os.fsencode(v['path'])),'original link shape');data[name]=dict(target=v,mode=st.st_mode,mtime_ns=st.st_mtime_ns,size=st.st_size)
 encoded=(json.dumps(dict(schema='exact-inactive-input-alias-root01',directory=str(directory),links=data),sort_keys=True,separators=(',',':'))+'\n').encode();require(len(encoded)<=16*1024**2,'bounded per-root alias DATA');roots.append((directory,overlay,data,encoded));print(json.dumps(dict(census_phase=ordinal,roots=len(roots),links=sum(len(x[2])for x in roots))),flush=True)
 require(sum(len(t[3])for t in roots)<=256*1024**2,'finite complete alias census')
require(roots and not CANCELLED,'nonempty bounded plan');g['checked_phase_close']();require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=512*1024**2,'light maintenance scratch reserve; verifier floor unchanged');(S/'archives').mkdir();fd=os.open(S,os.O_RDONLY);os.fsync(fd);os.close(fd);directories={};reclaimed_links=0
put(S/'plan01.json',dict(prior_guard=pin(P/'maintained/guard.py'),prior_config=pin(P/'config01.json'),roots=[dict(directory=str(d),overlay=o,links=len(v),decoded_bytes=len(b),decoded_sha256=hashlib.sha256(b).hexdigest())for d,o,v,b in roots],scope='Lossless obsolete OWNED inherited-input symlink metadata only; all regular objects, sources, receipts, logs, ledgers, claims and original metadata identities unchanged. Original link paths become honestly absent, recoverable from exact link target/mode/mtime DATA.'))
for i,(directory,overlay,data,encoded)in enumerate(roots):
 require(not CANCELLED,'cancellation before root publication');packed=lzma.compress(encoded,preset=6);require(len(packed)<=2*1024**2,'bounded archive');archive=S/'archives'/('phase-'+directory.parents[1].name+'.json.xz')
 with archive.open('xb')as f:f.write(packed);f.flush();os.fsync(f.fileno())
 d=lzma.LZMADecompressor();body=d.decompress(archive.read_bytes(),max_length=len(encoded)+1);require(d.eof and not d.unused_data and body==encoded,'exact bounded archive replay');record=dict(directory=str(directory),overlay=overlay,archive=pin(archive),decoded_bytes=len(encoded),decoded_sha256=hashlib.sha256(encoded).hexdigest(),links=len(data));put(archive.with_suffix('.identity.json'),record)
 # A durable full root record precedes every unlink; interrupted roots stay recoverable.
 for name,v in data.items():
  path=directory/name;require(path.is_symlink()and os.readlink(path)==v['target']['path']and path.lstat().st_mtime_ns==v['mtime_ns'],'unchanged original before unlink');path.unlink();reclaimed_links+=1
 fd=os.open(directory,os.O_RDONLY);os.fsync(fd);os.close(fd);require(all(not(directory/n).exists()and not(directory/n).is_symlink()for n in data),'all archived paths absent');directories[str(directory)]=record;put(S/('completed-root-'+str(i).zfill(4)+'.json'),record);print(json.dumps(dict(preserved_root=i,roots=len(roots),links=reclaimed_links,free_disk=os.statvfs(W).f_bavail*os.statvfs(W).f_frsize)),flush=True)
put(S/'aliases-manifest01.json',dict(schema='exact-inactive-input-alias-storage01',directories=directories,scope='Exact obsolete input aliases only, not regular objects or proof requalification.'))
put(S/'result01.json',dict(roots=len(directories),links=reclaimed_links,free_disk=os.statvfs(W).f_bavail*os.statvfs(W).f_frsize,regular_objects_sources_receipts_logs_ledgers_claims_unchanged=True,scope='Alias preservation only; zero Lean invocation or new kernel qualification.'))
print(json.dumps(dict(manifest=pin(S/'aliases-manifest01.json'),roots=len(directories),links=reclaimed_links,free_disk=os.statvfs(W).f_bavail*os.statvfs(W).f_frsize)))
