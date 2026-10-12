from pathlib import Path
import json,hashlib,runpy
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-field-official273-data01';P=W/'mac-full-arithmetic45-execution299';g=runpy.run_path(str(P/'maintained/guard.py'),run_name='read_only_definitions')
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def require(b,m):
 if not b:raise ValueError(m)
import lzma,os,sys
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated DATA')
table=json.loads((W/'mac-history-metadata-preservation126-44/archive-map01.json').read_bytes())['records']
def read(path):
 p=Path(path)
 if p.exists():return p.read_bytes()
 record=table[str(p)];require(pin(Path(record['archive']['path']))==record['archive'],'exact archived source');d=lzma.LZMADecompressor();raw=d.decompress(Path(record['archive']['path']).read_bytes(),max_length=record['original']['bytes']+1);require(d.eof and not d.unused_data and len(raw)==record['original']['bytes']and hashlib.sha256(raw).hexdigest()==record['original']['sha256'],'exact bounded original');return raw
import copy
v=json.loads(read(P/'config01.json'));C=copy.deepcopy(json.loads(read(v['base']['path'])));C.update(v['replace'])
for k,m in v['merge'].items():C[k].update(m)
require(hashlib.sha256((json.dumps(C,sort_keys=True,separators=(',',':'))+'\n').encode()).hexdigest()==v['effective_sha256'],'exact effective current config')
old=C['official'];require(pin(Path(old['path']))==old,'exact original manifest');o=json.loads(Path(old['path']).read_bytes());known=set(o['official_modules']);pending=['Mathlib.Algebra.Field.ZMod','Mathlib.NumberTheory.LucasPrimality'];added=[]
packages=Path(C['project'])/'.lake/packages';tool=Path(C['lean']).resolve().parents[1]
while pending:
 name=pending.pop()
 if name in known:continue
 path=g['first_package_file'](C['lean_path'],name)
 require(path is not None,'selected package');obj=Path(path);require(obj.is_file(),'official object exists')
 if obj.is_relative_to(tool):src=tool/'src/lean'/Path(name.replace('.','/')+'.lean');rel='lean4/'+str(src.relative_to(tool))
 else:
  package=next(p for p in packages.iterdir()if obj.is_relative_to(p));src=package/Path(name.replace('.','/')+'.lean');rel=str(src.relative_to(packages))
 require(src.is_file(),'primary source exists');metadata=obj.with_suffix('.ilean');data=json.loads(metadata.read_bytes());require(data['module']==name,'official metadata name')
 header=g['official_header'](src.read_bytes());deps=[r[0]for r in data['directImports']];pending.extend(set(header)|set(deps));known.add(name)
 o['manifest']['files'][rel]=pin(src)['sha256']
 for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
  q=obj.parent/(obj.stem+suffix);v=pin(q)if q.is_file()else None;o['slots'][str(q)]=v
  if v is not None:
   relative='lean4/'+str(q.relative_to(tool))if q.is_relative_to(tool)else str(q.relative_to(packages));o['manifest']['files'][relative]=v['sha256']
 added.append({'name':name,'source':pin(src),'metadata':pin(metadata),'direct_source_imports':header,'direct_object_imports':deps})
o['official_modules']=sorted(known);o['manifest']['modules']=len(known)
require(len(known)<=10000,'finite complete official closure');encoded=(json.dumps(o,sort_keys=True,separators=(',',':'))+'\n').encode();require(len(encoded)<=16*1024*1024,'unchanged finite official cap');require(not S.exists(),'immutable successor');stat=os.statvfs(W);require(stat.f_bavail*stat.f_frsize>=2*1024**3+len(encoded)+4*1024**2,'disk reserve before official-source write');S.mkdir();p=S/'official-union01.json';p.write_bytes(encoded)
(S/'qualification01.json').write_text(json.dumps({'prior':old,'successor':pin(p),'added':added,'scope':'SOURCE/object identity closure only; reused official prebuilt objects, no compiler execution'},sort_keys=True)+'\n');(S/'extend.py').write_bytes(Path(__file__).read_bytes());print(json.dumps({'manifest':pin(p),'added':[r['name']for r in added]}))
