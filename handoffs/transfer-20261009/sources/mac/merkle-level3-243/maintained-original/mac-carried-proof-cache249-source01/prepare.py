from pathlib import Path
import ast,hashlib,json,runpy,os,sys,copy
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-full-arithmetic45-execution271/maintained/guard.py';S=W/'mac-carried-proof-cache249-source01'
def require(c,m):
 if not c:raise RuntimeError(m)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated production primitive controls');require(not S.exists(),'fresh immutable source');require(pin(P)['sha256']=='2851e1c826d82a1e37784ece5e19a903680bf59d4b9db98448828b7b01f72807','exact safe predecessor')
old=P.read_text();new=old.replace('def carried_check(config):','def _carried_check_cold(config):',1);needle="            require(audit_log(read_pin(r['stdout']),[a['name'] for a in r['audits']])==r['audits'],'previous exact type/axiom audits')";require(new.count(needle)==1,'exact original audit guard');new=new.replace(needle,needle+"\n            checked_pin(r['stdout']) # register initial exact parsed-byte identity for every terminal check")
wrapper='''# Historical audit/keyset proof memoization within ONE dispatcher only.
# No object or raw log contents retained. Every hit binds exact counters,
# historical JSON and repair identities, ALL original directory tokens and
# registered file/archive change tokens. Full terminal checks still precede
# Popen and acceptance; current sources/imports/objects remain independently checked.
_CARRIED_PROOFS={}
_CARRIED_PROOF_BYTES=0
def carried_check(config):
    global _CARRIED_PROOF_BYTES
    key=(json.dumps(config['carried_failure'],sort_keys=True,separators=(',',':')),
         config['carried_attempts'],config['carried_lean_seconds'],
         json.dumps(config['history_closed_keyset_additions'],sort_keys=True,separators=(',',':')))
    remembered=_CARRIED_PROOFS.get(key)
    if remembered is not None:
        directories,identities,_=remembered
        for root,token in directories:
            require(directory_token(root)==token,'protected historical directory changed')
            require(root not in _DIRECTORY_PHASE or _DIRECTORY_PHASE[root]==token,'historical directory changed within phase')
            _DIRECTORY_PHASE[root]=token
        for path,signature in identities:
            require(_CHECKED.get(path)==signature,'protected historical identity proof missing/conflicting')
        return
    _carried_check_cold(config)
    checked_phase_close() # audit bytes/directory identities still exact after initial proof
    directories=tuple(_DIRECTORY_PHASE.items());identities=tuple(_CHECKED.items())
    charge=history_size((key,directories,identities))
    if len(_CARRIED_PROOFS)<8 and _CARRIED_PROOF_BYTES+charge<=32*1024*1024:
        _CARRIED_PROOFS[key]=(directories,identities,charge);_CARRIED_PROOF_BYTES+=charge

'''
require(new.count('def overlay_map(config):')==1,'exact wrapper placement');new=new.replace('def overlay_map(config):',wrapper+'def overlay_map(config):',1)
a={n.name:ast.dump(n,include_attributes=False)for n in ast.parse(old).body if isinstance(n,ast.FunctionDef)};b={n.name:ast.dump(n,include_attributes=False)for n in ast.parse(new).body if isinstance(n,ast.FunctionDef)};require(set(b)==set(a)|{'_carried_check_cold'} and [k for k in a if a[k]!=b[k]]==['carried_check'],'only original carried_check entry changed');require(ast.dump(ast.parse(new),include_attributes=False),'source parses')
st=os.statvfs(W);require(st.f_bavail*st.f_frsize>=2*1024**3+1048576,'disk reserve');S.mkdir();(S/'guard.py').write_text(new);(S/'prepare.py').write_bytes(Path(__file__).read_bytes());success=Path(W/'mac-full-arithmetic45-execution271/runtime/receipts/1487-CapturedMerkleFirstSparse245B22.json');real=json.loads(success.read_bytes());stdout=Path(real['stdout']['path']).read_bytes();cases=[]
def setup(label):
 root=S/'fixtures'/label;protected=root/'protected';protected.mkdir(parents=True);out=protected/'stdout';out.write_bytes(stdout);obj=protected/'object';obj.write_bytes(b'DATA_ONLY_NOT_LEAN');r=dict(status='passed',exit=0,error=None,cleanup=dict(clean=True,leader_reaped=True),fresh_execution_credit=0,lean_seconds=1.25,stdout=pin(out),audits=real['audits'],objects={str(obj):pin(obj)});receipt=protected/'receipt.json';receipt.write_text(json.dumps(r,sort_keys=True,separators=(',',':'))+'\n');entries={str(p):pin(p)for p in protected.iterdir()};h=root/'history.json';h.write_text(json.dumps(dict(roots=[str(protected)],entries=entries,parents=[],receipts=[pin(receipt)],expected_statuses=['passed'],consumed_attempts=1,consumed_lean_seconds=1.25),sort_keys=True,separators=(',',':'))+'\n');ns=runpy.run_path(str(S/'guard.py'),run_name='SOURCE_DATA_ONLY');addition='/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/mac-full-arithmetic45-execution186/config01.json';records=ns['preserved_configs']();config=dict(carried_failure=pin(h),carried_attempts=1,carried_lean_seconds=1.25,history_closed_keyset_additions={addition:records[addition]['original']});count=[0];audit=ns['audit_log']
 # runpy returns a globals copy; functions retain their defining globals.
 g=ns['carried_check'].__globals__;g['audit_log']=lambda *a:(count.__setitem__(0,count[0]+1),audit(*a))[1];g['carried_check'](config);require(count[0]==1 and len(g['_CARRIED_PROOFS'])==1,'initial exact actual audit and proof recorded');g['_DIRECTORY_PHASE'].clear();g['carried_check'](config);g['checked_phase_close']();require(count[0]==1,'unchanged history reuses proof only after terminal identities');return root,protected,out,obj,receipt,h,config,g,count
root,protected,out,obj,receipt,h,c,g,count=setup('positive');cases.append(dict(case='initial-audit-and-unchanged-terminal-hit',passed=True,actual_audit_calls=count[0],cache_bytes=g['_CARRIED_PROOF_BYTES']))
for label,mutation,reason in [('wrong-count',lambda c:c.update(carried_attempts=2),'exact protected previous consumption'),('wrong-time',lambda c:c.update(carried_lean_seconds=2),'exact protected previous consumption'),('wrong-history-pin',lambda c:c['carried_failure'].update(sha256='0'*64),'conflicting pinned identity')]:
 root,protected,out,obj,receipt,h,c,g,count=setup(label);mutation(c)
 try:g['carried_check'](c);g['checked_phase_close']();raise AssertionError('bad context accepted')
 except RuntimeError as e:require(reason in str(e),'exact intended context refusal');cases.append(dict(case=label,refused=str(e)))
for label,which in [('stdout-restored-mtime','stdout'),('object-restored-mtime','object'),('receipt-restored-mtime','receipt'),('history-restored-mtime','history')]:
 root,protected,out,obj,receipt,h,c,g,count=setup(label);p={'stdout':out,'object':obj,'receipt':receipt,'history':h}[which];st=p.stat();raw=p.read_bytes();p.write_bytes(bytes([raw[0]^1])+raw[1:]);os.utime(p,ns=(st.st_atime_ns,st.st_mtime_ns));g['_DIRECTORY_PHASE'].clear()
 try:g['carried_check'](c);g['checked_phase_close']();raise AssertionError('changed bytes accepted')
 except RuntimeError as e:require('phase identity changed' in str(e),'terminal token refusal');cases.append(dict(case=label,refused=str(e)))
for label,mutation in [('new-file',lambda p:(p/'new').write_bytes(b'new')),('removed-file',lambda p:(p/'object').unlink()),('changed-link',lambda p:((p/'object').unlink(),(p/'object').symlink_to(str(p/'stdout'))))]:
 root,protected,out,obj,receipt,h,c,g,count=setup(label);mutation(protected);g['_DIRECTORY_PHASE'].clear()
 try:g['carried_check'](c);g['checked_phase_close']();raise AssertionError('changed directory accepted')
 except RuntimeError as e:require('protected historical directory changed' in str(e),'directory token refusal');cases.append(dict(case=label,refused=str(e)))
require(len(cases)==11,'eleven actual isolated production helper controls')
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
put('controls01.json',dict(scope='Actual cold/warm production carried_check + checked_phase_close, copied original standard-axiom log, SYNTHETIC DATA_ONLY receipt/object histories; no guard execute/Popen/runtime/Lean. All fixture status-passed labels are synthetic and confer no qualification. Eleven controls; archive-original absence remains unchanged246 primitive.',cases=cases));put('delta01.json',dict(old=pin(P),new=pin(S/'guard.py'),functions=['carried_check'],added_functions=['_carried_check_cold'],contract='Exact initial original audit/history/keyset/counter verification once per frozen context. All ordinary/archived byte change stamps AND every historical directory token retained; directory tokens rechecked on each hit, file/archive/absence tokens rechecked by unchanged terminal pre/post routine beforePopen and acceptance. Current own state/import/source/resource/cleanup checks untouched. Eight contexts/32MiB maximum, no object/raw contents retained, no cross-process cache.',physical_limits_unchanged=True));files={}
for p in S.rglob('*'):
 if p.is_symlink():files[str(p.relative_to(S))]=dict(path=str(p),symlink_target=os.readlink(p),target=pin(p.resolve()))
 elif p.is_file():files[str(p.relative_to(S))]=pin(p)
put('producer-manifest01.json',files);put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')));print(json.dumps(dict(stage=str(S),guard=pin(S/'guard.py'),producer=pin(S/'producer-manifest01.json'),controls=len(cases))))
