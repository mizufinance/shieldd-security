from pathlib import Path
import sys,json,hashlib,os,runpy,urllib.request,ast
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');R=W.parent;S=W/'mac-official-cache277-restoration01'
def require(v,m):
 if not v:raise RuntimeError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'flags');require(not S.exists(),'immutable restoration plan');ns=runpy.run_path('/tmp/inspect_cache_capacity275_02.py',run_name='READ_ONLY_CAPACITY');old=R/'outputs/mac-subgroup-prime06/official-imports-9b6f311a61ef19f3.json';require(pin(old)['sha256']=='9b6f311a61ef19f3eea88bc98f91b3a82469e00b2c7a8b65e1cafaf4e91826f6','exact old official identity manifest');m=json.loads(old.read_bytes());packages=Path(ns['ns']['packages']);records=[]
for name,d in ns['missing'].items():
 archive=Path(d['archives'][0]);source=Path(d['source']);obj=Path(d['object']);package=next(p for p in packages.iterdir()if obj.is_relative_to(p));relative=str(source.relative_to(packages));require(pin(source)['sha256']==m['files'][relative],'same exact official SOURCE');wanted={}
 for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
  path=obj.parent/(obj.stem+suffix);relative=str(path.relative_to(packages));digest=m['files'].get(relative);require(not path.exists()and not path.is_symlink(),'new restore only absent current companion');wanted[suffix]=dict(path=str(path),sha256=digest)
 require(wanted['.olean']['sha256']and wanted['.ilean']['sha256'],'official object/metadata historical identities');records.append(dict(module=name,archive=pin(archive),source=pin(source),package=str(package.resolve()),object=str(obj),wanted=wanted,capacity_bound=next(v['capacity_bound']for v in ns['estimates']if v['module']==name)))
require(len(records)==627,'closed exact missing closure');require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=2*1024**3+4*1024**2,'plan only disk floor');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'dictionary.bin').write_bytes(ns['dictionary']);(S/'capacity-parser.py').write_bytes(Path('/tmp/inspect_cache_capacity275_02.py').read_bytes());tool=Path('/Users/antoinecyr/.elan/toolchains/leanprover--lean4---v4.30.0/bin/leantar');put('plan01.json',dict(schema='exact-official-cache-restoration277',records=records,total_capacity_bound=sum(v['capacity_bound']for v in records),tool=pin(tool),dictionary=pin(S/'dictionary.bin'),old_official_manifest=pin(old),current_official_manifest=pin(Path(ns['ns']['c']['official']['path'])),scope='Restore only absent official object companions from already downloaded exact LTR3 inputs; compare every output SHA against original same Lean4.30/c5ea003 manifest. ZERO new compiler qualification; existing files never overwritten. Temporary leantar outputs/copies counted and disposable after exact inventory journal. No automatic Lean dispatch.'))
put('producer-plan01.json',{str(p.relative_to(S)):pin(p)for p in S.iterdir()if p.is_file()});print(json.dumps(dict(stage=str(S),records=len(records),plan=pin(S/'plan01.json'),capacity=sum(v['capacity_bound']for v in records),status='SOURCE_ONLY_RESTORER_PENDING_NO_EXTRACTION')))
