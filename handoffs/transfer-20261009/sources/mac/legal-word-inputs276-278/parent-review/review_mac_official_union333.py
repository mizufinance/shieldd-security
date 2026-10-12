from pathlib import Path
import hashlib,json,copy,runpy
J=Path(__file__).parent;W=J.parent;S=W/'mac-field-official273-data01'
def pin(p):
 p=Path(p);assert p.is_file()and not p.is_symlink();h=hashlib.sha256()
 with p.open('rb')as f:
  while b:=f.read(1024*1024):h.update(b)
 return dict(path=str(p),bytes=p.stat().st_size,sha256=h.hexdigest())
def read(v):assert pin(v['path'])==v;return json.loads(Path(v['path']).read_bytes())
q=json.loads((S/'qualification01.json').read_bytes());prior=read(q['prior']);union=read(q['successor']);assert q['successor']['sha256']=='428e4a7cf4b27fd53ff80a449d277678125050f76f89553c430240fd1a310872'
oldpin=json.loads((W/'mac-official-cache277-restoration03/result01.json').read_bytes())['old_manifest'];old=read(oldpin);assert old['revisions']==union['manifest']['revisions']
g=runpy.run_path(str(W/'mac-full-arithmetic45-execution309/maintained/guard.py'),run_name='SOURCE_ONLY')
expected=copy.deepcopy(prior);names=set(prior['official_modules']);added={};deps={};unmatched_ir=[]
def key(p):return str(p).split('/.lake/packages/',1)[1]
for entry in q['added']:
 name=entry['name'];assert name not in names and name not in added and not name.startswith('ShielddSecurity.');added[name]=entry
 for kind in ['source','metadata']:
  v=entry[kind];assert pin(v['path'])==v and old['files'][key(v['path'])]==v['sha256']
 src=Path(entry['source']['path']);obj=Path(entry['metadata']['path']).with_suffix('.olean');sourceimports=g['official_header'](src.read_bytes());meta=json.loads(Path(entry['metadata']['path']).read_bytes());objectimports=[r[0]for r in meta['directImports']]
 assert meta['module']==name and sourceimports==entry['direct_source_imports'] and objectimports==entry['direct_object_imports'];deps[name]=set(sourceimports)|set(objectimports)
 expected['manifest']['files'][key(src)]=entry['source']['sha256']
 for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
  p=obj.parent/(obj.stem+suffix);v=pin(p)if p.is_file()else None;assert not p.is_symlink();expected['slots'][str(p)]=v
  if v is not None:
   if key(p) in old['files']:assert old['files'][key(p)]==v['sha256']
   else:assert suffix=='.ir';unmatched_ir.append(v)
   expected['manifest']['files'][key(p)]=v['sha256']
 names.add(name)
assert len(added)==669 and len(names)==3612
pending=['Mathlib.Algebra.Field.ZMod','Mathlib.NumberTheory.LucasPrimality'];reached=set(prior['official_modules'])
while pending:
 name=pending.pop()
 if name in reached:continue
 assert name in added;reached.add(name);pending.extend(deps[name])
assert reached==names
expected['official_modules']=sorted(names);expected['manifest']['modules']=len(names);assert expected==union
report=dict(status='PASSED',prior=q['prior'],successor=q['successor'],historical_official_manifest=oldpin,added_modules=669,complete_modules=3612,slot_records=len(union['slots']),unmatched_auxiliary_ir=unmatched_ir,scope='Exact prior floor fields and slots retained. Every669 added primary source/metadata/kernel companion matched both physical bytes and older same-revision official manifest. Auxiliary .ir records absent from that historical manifest are separately inventoried as physical identity only, not official-cache matched. Actual source headers and .ilean direct imports checked, exact transitive closure from ZMod/LucasPrimality reconstructed, no custom ShielddSecurity module admitted as official. Full successor data equals independent deterministic extension. Metadata/object identity only; no declaration/type/axiom or new compiler qualification and full Transfer remains OPEN.',full_transfer='OPEN')
out=J/'mac-official-union-review333.json';assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n');print('PASSED exact669 additions/full3612 official closure')
