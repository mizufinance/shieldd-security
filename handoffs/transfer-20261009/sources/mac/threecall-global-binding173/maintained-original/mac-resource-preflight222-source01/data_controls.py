from pathlib import Path
import ast,json,hashlib,difflib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-full-arithmetic45-execution220';S=W/'mac-resource-preflight222-source01'
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=Path(p).read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(path,v):
 with path.open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
old=(P/'maintained/guard.py').read_text();require(pin(P/'maintained/guard.py')['sha256']=='cc900fcc6e04d03ceab5c14d686323fcce1cf9e45d597a4f591ee257cbf50bc0','exact predecessor')
helper='''def physical_preflight(config):
    # Early admission only; full artifact census remains immediately pre-Popen
    # under owned lock and after compilation and final receipt publication.
    stat=os.statvfs(config['batch_root']); disk=stat.f_bavail*stat.f_frsize
    memory=free_memory()
    require(disk>=2*1024*1024*1024 and memory>=15, 'RAM/disk admission')
    return {'free_memory_percent':memory,'free_disk_bytes':disk}

'''
new=old.replace('def bounds(config):',helper+'def bounds(config):',1)
needle='cancelled();pre=bounds(config);launch_reserve(pre)';require(new.count(needle)==3,'exact three prelaunch censuses')
new=new.replace(needle,'cancelled();physical_preflight(config)',2)
new=new.replace('if not cache.exists(): initialize_overlay(config)','if not cache.exists():\n            pre=bounds(config);launch_reserve(pre);initialize_overlay(config)',1)
oldkey="actual.update(key for key in preserved_configs() if any(pathlib.Path(key).is_relative_to(pathlib.Path(root)) for root in roots))"
newkey="require(all(root.startswith('/') and '..' not in root.split('/') and '//' not in root and not root.endswith('/') for root in roots), 'canonical historical directory roots')\n        actual.update(key for key in preserved_configs() if any(key.startswith(root+'/') for root in roots))"
require(new.count(oldkey)==1,'exact archive keyset predicate');new=new.replace(oldkey,newkey,1)
# Unchanged theorem/source/type/import/audit/process ownership and terminal checks.
oldast=ast.parse(old);newast=ast.parse(new);of={n.name:ast.dump(n)for n in oldast.body if isinstance(n,ast.FunctionDef)};nf={n.name:ast.dump(n)for n in newast.body if isinstance(n,ast.FunctionDef)}
require({n for n in of if of[n]!=nf[n]}=={'execute','carried_check'} and set(nf)-set(of)=={'physical_preflight'},'exact minimal function delta')
require('aggregate_lean_seconds'not in new and 'total_attempts'not in new,'no campaign quotas')
# PURE mocked primitive checks; no subprocess or executor entrypoint.
g=dict(os=type('MockOS',(),{})(),free_memory=lambda:15,require=require)
exec(helper,g);count=0
for disk,mem,accept in [(2*1024**3,15,True),(2*1024**3-1,15,False),(2*1024**3,14,False),(3*1024**3,90,True)]:
 g['os'].statvfs=lambda p,d=disk:type('V',(),{'f_bavail':d,'f_frsize':1})();g['free_memory']=lambda m=mem:m
 try:g['physical_preflight']({'batch_root':'mock-only'});require(accept,'intended refusal missing')
 except ValueError as e:require(not accept and str(e)=='RAM/disk admission','exact intended resource reason')
 count+=1
# Actual frozen root/pin metadata, no guard or helper main/Lean launch.
import lzma
storage=json.loads((W/'mac-history-metadata-preservation126-28/archive-map01.json').read_bytes())['records']
c=json.loads((P/'config01.json').read_bytes());todo=[c['carried_failure']];roots=[]
while todo:
 identity=todo.pop();p=Path(identity['path'])
 if p.exists():b=p.read_bytes()
 else:
  record=storage[str(p)];compressed=Path(record['archive']['path']).read_bytes();require(pin(record['archive']['path'])==record['archive'],'exact archive')
  dec=lzma.LZMADecompressor();b=dec.decompress(compressed,max_length=identity['bytes']+1);require(dec.eof and not dec.unused_data,'exact metadata EOF')
 require(len(b)==identity['bytes']and hashlib.sha256(b).hexdigest()==identity['sha256'],'exact frozen metadata')
 h=json.loads(b);todo+=h.get('parents',[]);roots+=h['roots']
for root in roots:
 require(root.startswith('/')and '..'not in root.split('/')and '//'not in root and not root.endswith('/'),'canonical actual root')
 require({k for k in storage if Path(k).is_relative_to(Path(root))}=={k for k in storage if k.startswith(root+'/')},'archive keyset exact predicate parity')
require(not S.exists(),'new immutable source delta');S.mkdir();(S/'physical-preflight.py').write_text(helper);(S/'guard.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='guard220.py',tofile='guard223.py')));(S/'data_controls.py').write_bytes(Path(__file__).read_bytes())
put(S/'data-report01.json',dict(scope='PURE_SOURCE_DATA_ONLY; no guard/dispatcher/Lean invocation',mock_resource_cases=count,actual_archive_root_parity=len(roots),archive_records=len(storage),changed_functions=['execute','carried_check'],new_functions=['physical_preflight'],full_fixed_prepost_unchanged=True,immediate_prePopen_artifact_census_unchanged=True,postmodule_and_finalreceipt_census_unchanged=True,overlay_initialization_reserve_retained=True,derived_guard_bytes=len(new.encode()),derived_guard_sha256=hashlib.sha256(new.encode()).hexdigest(),old=pin(P/'maintained/guard.py'),zero_formal_credit=True))
put(S/'producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.iterdir()if p.is_file()});put(S/'envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put(S/'postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(stage=str(S),producer=pin(S/'producer-manifest01.json'),report=pin(S/'data-report01.json'))))
