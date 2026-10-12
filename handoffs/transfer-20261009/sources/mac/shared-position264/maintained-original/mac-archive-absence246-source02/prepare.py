from pathlib import Path
import ast,hashlib,json,lzma,os,sys
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-full-arithmetic45-execution269/maintained/guard.py';S=W/'mac-archive-absence246-source02'
def require(c,m):
 if not c:raise RuntimeError(m)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated source controls');require(pin(P)['sha256']=='d0d0d2c9058d660591e40eac1aded7106d3c9d2ce94b219f17f115bd2c036af8','exact previous guard');require(not S.exists(),'fresh immutable repair')
old=P.read_text();new=old.replace("    if remembered is not None:\n        require(remembered[-2:]", "    if remembered is not None:\n        if remembered[0]=='archive':\n            original=pathlib.Path(identity['path'])\n            require(not original.exists() and not original.is_symlink(), 'archived original reappeared')\n        require(remembered[-2:]")
needle="        if signature[0]=='archive':\n            p=pathlib.Path(preserved_configs()[key]['archive']['path']);expected=signature[1:7]"
replacement="        if signature[0]=='archive':\n            original=pathlib.Path(key)\n            require(not original.exists() and not original.is_symlink(), 'archived original reappeared at terminal check')\n            p=pathlib.Path(preserved_configs()[key]['archive']['path']);expected=signature[1:7]"
require(new.count(needle)==1,'exact terminal archive context');new=new.replace(needle,replacement);before=ast.parse(old);after=ast.parse(new);functions=lambda t:{n.name:ast.dump(n,include_attributes=False)for n in t.body if isinstance(n,ast.FunctionDef)};a=functions(before);b=functions(after);require(set(a)==set(b) and [k for k in a if a[k]!=b[k]]==['checked_pin','checked_phase_close'],'only two maintained identity primitives change')
stat=os.statvfs(W);require(stat.f_bavail*stat.f_frsize>2*1024**3+1048576,'disk margin');S.mkdir();(S/'guard.py').write_text(new);(S/'prepare.py').write_bytes(Path(__file__).read_bytes());cases=[]
selected=[n for n in after.body if isinstance(n,(ast.Import,ast.ImportFrom)) or isinstance(n,ast.FunctionDef)and n.name in ['require','sha','strict_json','read_pin','checked_pin','checked_phase_close']]
def fixture(label):
 root=S/'fixtures'/label;root.mkdir(parents=True);original=root/'original.json';archive=root/'packed.xz';archive.write_bytes(lzma.compress(b'{}\n'));record=dict(original=dict(path=str(original),bytes=3,sha256=hashlib.sha256(b'{}\n').hexdigest()),archive=pin(archive));ns=dict(_CHECKED={},_ARCHIVE_PROOFS=set(),directory_phase_close=lambda:None,preserved_configs=lambda:{str(original):record});exec(compile(ast.Module(body=selected,type_ignores=[]),'actual selected production identity primitives','exec'),ns);ns['checked_pin'](record['original']);ns['checked_phase_close']();return root,original,archive,record,ns
for label,mutation in [('ordinary-wrong',lambda r,o,a:o.write_bytes(b'bad')),('ordinary-exact',lambda r,o,a:o.write_bytes(b'{}\n')),('symlink-present',lambda r,o,a:(r/'target').write_bytes(b'bad')or o.symlink_to('target')),('symlink-dangling',lambda r,o,a:o.symlink_to('missing'))]:
 root,o,archive,record,ns=fixture(label)
 if label=='symlink-present':(root/'target').write_bytes(b'bad');o.symlink_to('target')
 else:mutation(root,o,archive)
 for f,args in [('checked_pin',(record['original'],)),('checked_phase_close',())]:
  try:ns[f](*args);raise AssertionError('mutation accepted')
  except RuntimeError as e:require('archived original reappeared' in str(e),'exact intended absence reason');cases.append(dict(case=label+'-'+f,refused=str(e)))
 # Retain symlink bytes; append its synthetic target only AFTER the dangling-link refusal observations.
 if label=='symlink-dangling':(root/'missing').write_bytes(b'owned synthetic target after refusal')
root,o,archive,record,ns=fixture('unchanged');ns['checked_pin'](record['original']);ns['checked_phase_close']();cases.append(dict(case='unchanged-archive-absence',passed=True))
root,o,archive,record,ns=fixture('archive-restored-mtime');st=archive.stat();archive.write_bytes(archive.read_bytes());os.utime(archive,ns=(st.st_atime_ns,st.st_mtime_ns))
try:ns['checked_phase_close']();raise AssertionError('archive metadata mutation accepted')
except RuntimeError as e:require('phase identity changed' in str(e),'exact archive ctime refusal');cases.append(dict(case='archive-restored-mtime',refused=str(e)))
require(len(cases)==10,'ten actual pure source controls');(S/'controls01.json').write_text(json.dumps(dict(scope='Ten actual AST-selected production primitive controls on new isolated filesystem fixtures; no guard entrypoint/runtime/cache/intent/process/Lean. Directory checks remain unchanged and are outside these primitive cases.',cases=cases,old=pin(P),new=pin(S/'guard.py')),sort_keys=True,separators=(',',':'))+'\n');(S/'delta01.json').write_text(json.dumps(dict(functions=['checked_pin','checked_phase_close'],contract='Cached archived-original proof requires original remain absent including dangling symlinks, both cache access and EVERY terminal pre/post check. Exact compressed archive metadata and initial SHA/size/EOF checks unchanged. All other functions/machine limits/source audits/ownership unchanged.',old=pin(P),new=pin(S/'guard.py')),sort_keys=True,separators=(',',':'))+'\n')
files={}
for p in S.rglob('*'):
 if p.is_symlink():files[str(p.relative_to(S))]=dict(path=str(p),symlink_target=os.readlink(p),target=pin(p.resolve())if p.exists()else None)
 elif p.is_file():files[str(p.relative_to(S))]=pin(p)
def put(name,value):
 with(S/name).open('x')as f:f.write(json.dumps(value,sort_keys=True,separators=(',',':'))+'\n')
put('producer-manifest01.json',files)
put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')))
put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(stage=str(S),guard=pin(S/'guard.py'),producer=pin(S/'producer-manifest01.json'),controls=len(cases))))
