"""Independent official kernel payload identity and exact load-layout metadata review."""
from pathlib import Path
import json,hashlib,re,subprocess
J=Path(__file__).parent;G=J.parent/'shared-build-handoff';D=J/'windows-external-floor08-review01';P=D/'packet01';C=J/'windows-scalar-inverse-correctness-review01/packet01'
sha=lambda b:hashlib.sha256(b).hexdigest()
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=sha(b))
def strict(b):
 def unique(ps):
  out={}
  for k,v in ps:assert k not in out;out[k]=v
  return out
 return json.loads(b,object_pairs_hook=unique)
manifest=strict((P/'manifest.json').read_bytes());assert manifest['kind']=='EXISTING_OFFICIAL_EXTERNAL_FLOOR08_LOSSLESS_DATA_TRANSPORT'and not manifest['proof_replay']and manifest['object_bytes_in_archive']==0 and len(manifest['entries'])==45
for e in manifest['entries']:
 b=(P/e['archive_path']).read_bytes();v=e['original'];assert len(b)==v['bytes']and sha(b)==v['sha256']
fpath=P/'original/transfer-external-floor-complete-20261010-08/external-floor.json';oldpath=P/'original/transfer-external-floor-complete-20261010-06/external-floor.json';f=strict(fpath.read_bytes());old=strict(oldpath.read_bytes());plan=strict((C/'qualified/plan.json').read_bytes())
assert pin(fpath)['bytes']==plan['external_floor']['bytes']==12241910 and pin(fpath)['sha256']==plan['external_floor']['sha256']=='82ef07658ca7d127e3e58c293946c87dfdb66dba4a94ad2683c9c7158e92ba72'
assert f['admission_ready']and old['admission_ready']and not f['gaps']and len(f['modules'])==3612 and len(f['immutable_files'])==20202
refs={};published_refs=[]
for name,relative in [('official_reference','official-references/official_reference.json'),('lucas_field_official_reference','official-references/lucas_field_official_reference.json')]:
 p=P/relative;v=f[name];assert pin(p)['bytes']==v['bytes']and pin(p)['sha256']==v['sha256'];d=strict(p.read_bytes());assert d['revisions']['mathlib']=='c5ea00351c28e24afc9f0f84379aa41082b1188f'
 tail=v['path'].split('\\handoffs\\',1)[1].replace('\\','/');published=G/'handoffs'/tail;assert published.read_bytes()==p.read_bytes();assert subprocess.check_output(['git','show','HEAD:'+str(published.relative_to(G))],cwd=G)==p.read_bytes();published_refs.append(pin(published))
 for k,h in d['files'].items():
  if k in refs:assert refs[k]==h
  refs[k]=h
qpath=P/'original/transfer-cache-qualified78-20261010-01/qualification.json';q=strict(qpath.read_bytes());assert pin(qpath)['bytes']==f['additional_official_reference']['bytes']and pin(qpath)['sha256']==f['additional_official_reference']['sha256']and q['admission_ready']and not q['mismatches']and len(q['records'])==78
for k,h in q['files'].items():
 if k in refs:assert refs[k]==h
 refs[k]=h
for r in q['records']:
 for z in r['objects']:assert all(z['existing'][k]==z['extracted'][k]for k in ['bytes','sha256'])
comppath=P/'original/transfer-external-package-overlay-20261010-03/composition-review.json';comp=strict(comppath.read_bytes());assert pin(comppath)['bytes']==f['first_package_composition']['bytes']and pin(comppath)['sha256']==f['first_package_composition']['sha256'];assert len(comp['created_hardlinks'])==13 and len(comp['junctions'])==16
aliases={r['alias']['path']:r['source']for r in comp['created_hardlinks']}
for r in comp['created_hardlinks']:assert all(r['source'][k]==r['alias'][k]for k in ['bytes','sha256'])
assert set(f['modules'])==set(old['modules'])and f['direct_source_imports']==old['direct_source_imports']and f['root_modules']==old['root_modules']
changed=[];required=source_count=auxiliary=0;allpins={}
for n,m in f['modules'].items():
 prior=old['modules'][n];assert m['source']==prior['source']and m['imports']==prior['imports']and m['implicit_Init']==prior['implicit_Init']and len(m['objects'])==len(prior['objects'])
 for a,b in zip(prior['objects'],m['objects']):
  assert all(a[k]==b[k]for k in ['bytes','sha256'])
  if a['path']!=b['path']:assert aliases[b['path']]==a;changed.append(b['path'])
 src=m['source'];raw=src['path'];key=('lean4/'+raw.split('leanprover--lean4---v4.30.0\\',1)[1])if'leanprover--lean4---v4.30.0\\'in raw else raw.split('\\.lake\\packages\\',1)[1];key=key.replace('\\','/');pkg=key.split('/')[0];assert refs[key]==src['sha256'];source_count+=1
 assert not n.startswith('ShielddSecurity.')
 assert all(c in f['modules']for c in m['imports'])and(not m['implicit_Init']or'Init'in f['modules'])
 for r in [src,*m['objects']]:
  assert 0<=r['bytes']and re.fullmatch('[0-9a-f]{64}',r['sha256'])
  if r['path']in allpins:assert allpins[r['path']]==r
  allpins[r['path']]=r
 for r in m['objects']:
  if pkg=='lean4':k='lean4/'+r['path'].split('leanprover--lean4---v4.30.0\\',1)[1].replace('\\','/')
  else:
   stem=n.replace('.','\\');suffix=r['path'][r['path'].rindex(stem)+len(stem):];k=pkg+'/.lake/build/lib/lean/'+n.replace('.','/')+suffix
  if k in refs:assert refs[k]==r['sha256'];required+=1
  else:assert k.endswith('.ir');auxiliary+=1
assert len(allpins)==20202 and {r['path']:r for r in f['immutable_files']}==allpins and len(changed)==13 and auxiliary==3534 and required+source_count==16668
direct=['Mathlib.Data.Fintype.Units','Mathlib.GroupTheory.OrderOfElement'];assert all(n in f['modules']for n in direct);seen=set()
def visit(n):
 if n in seen:return
 seen.add(n);m=f['modules'][n]
 for c in m['imports']:visit(c)
 if m['implicit_Init']:visit('Init')
for n in direct:visit(n)
floor_root='C:\\src\\shieldd-formal\\.work\\diagnostics\\transfer-external-package-overlay-20261010-03\\modules';assert plan['lean_path'][2]==floor_root and plan['lean_path'][3]=='C:\\src\\shieldd-formal\\.work\\diagnostics\\transfer-implementation-20261002\\windows-jubjub-isolated-05\\modules'
toolchain=(P/'original-circuits/lean-toolchain').read_text().strip();assert toolchain=='leanprover/lean4:v4.30.0';lake=strict((P/'original-circuits/lake-manifest.json').read_bytes());assert next(z['rev']for z in lake['packages']if z['name']=='mathlib')=='c5ea00351c28e24afc9f0f84379aa41082b1188f'
out=D/'official-floor-identity-review01.json';assert not out.exists();report=dict(status='PASSED',kind='Exact transported official source/required kernel object inventory and first-package load identity review; no verifier/cache extraction executed',floor=pin(fpath),prior_floor=pin(oldpath),manifest=pin(P/'manifest.json'),original_package_composition=pin(comppath),additional_cache_qualification=pin(qpath),published_official_references=published_refs,modules=3612,recorded_immutable_files=20202,official_sources_matched=source_count,official_object_payloads_matched=required,auxiliary_ir_observed_without_published_reference=auxiliary,changed_object_paths_exact_hardlinks=13,direct_new_imports=direct,recursive_new_import_modules=len(seen),lean_toolchain=toolchain,mathlib_sha='c5ea00351c28e24afc9f0f84379aa41082b1188f',scope='Exact floor08 is floor06 with thirteen byte-identical object hardlink path changes and complete original first-package composition; all imports recursively closed. Every source and required olean/private/server payload matches published official references plus original qualified78-module cache extraction.3534 auxiliary IR files are original recorded/protected identities, not independently matched official references; no native/IR execution or remote file rehash is claimed. Existing guarded same-host inventory observations remain historical, not fresh Root replay. Physical runner/limits checked at consuming endpoint separately. Kernel source theorem scope/native/private-generated/full Transfer boundaries unchanged.',full_transfer='OPEN')
out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(status='PASSED',modules=3612,sources=source_count,object_payloads=required,auxiliary_ir=auxiliary,recursive_imports=len(seen))))
