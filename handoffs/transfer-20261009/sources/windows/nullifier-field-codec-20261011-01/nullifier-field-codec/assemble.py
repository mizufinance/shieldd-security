from pathlib import Path
import hashlib, importlib.util, io, json, re, tarfile
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
CURRENT=DIAG/'transfer-nullifier-field-codec-20261012-03'
CHECKPOINT=DIAG/'transfer-nullifier-field-codec-checkpoint-20261012-03'
MODULE='TransferNullifierFieldCodec01'
PARENT=DIAG/'transfer-scalar-choice-correspondence-endpoint-20261012-02'
archive=ROOT/'portable-windows-nullifier-field-codec-endpoint01.tar.xz'
def pin(p):
 p=Path(p);b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def dump(p,o):p.write_bytes((json.dumps(o,indent=2,sort_keys=True)+'\n').encode())
assert not archive.exists() and not (ROOT/'manifest.json').exists()
spec=importlib.util.spec_from_file_location('codec_auditor',CURRENT/'execute_bounded.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
plan=json.loads((CURRENT/'plan.json').read_bytes());events=[json.loads(x) for x in (CURRENT/'events.jsonl').read_text().splitlines()]
assert len(events)==2 and events[-1]['result']['status']=='passed'
stdout=CURRENT/('runs/01-'+MODULE+'/stdout.txt');fresh=m.audit(stdout.read_text(),plan['targets'][0]['audit_names'])
assert len(fresh)==10 and fresh==events[-1]['result']['audits'] and pin(stdout)==events[-1]['result']['stdout']
for obj in events[-1]['result']['objects']:assert pin(obj['path'])==obj
kinds=re.findall(r'^(def|theorem|structure|inductive) ',m.code_only((CURRENT/('handwritten/'+MODULE+'.lean')).read_text()),re.M)
assert len(kinds)==10 and kinds.count('def')==2 and kinds.count('theorem')==8
pool=json.loads(Path(plan['owned_import_pool']['path']).read_bytes());assert pool['objects']==208 and len(pool['inherited_public_reports'])==1473
parent_archive=PARENT/'portable-windows-scalar-choice-correspondence-endpoint01.tar.xz'
assert pin(parent_archive)['sha256']=='342a74d38b2133d0cad45b1e79ede9fa6957731bf8cfa5f208e2277747dfbad1'
with tarfile.open(parent_archive,'r:xz') as t:
 parent_review=json.loads(t.extractfile('review.json').read());parent_pool=json.loads(t.extractfile('context/owned-composition-review.json').read())
 parent_plan=json.loads(t.extractfile('qualified/plan.json').read());parent_events=[json.loads(x) for x in t.extractfile('qualified/events.jsonl').read().decode().splitlines()]
 parent_raw=t.extractfile('reports/fresh-6-complete-declarations.txt').read().decode();parent_reports=m.audit(parent_raw,parent_plan['targets'][0]['audit_names'])
 parent_manifest=json.loads(t.extractfile('manifest.json').read())
 for row in parent_manifest['entries']:
  raw=t.extractfile(row['archive_path']).read();assert len(raw)==row['original']['bytes'] and hashlib.sha256(raw).hexdigest()==row['original']['sha256']
assert json.loads((PARENT/'review.json').read_bytes())==parent_review
assert parent_reports==parent_review['fresh_audits']==parent_events[-1]['result']['audits'] and len(parent_reports)==6
assert pool['inherited_public_reports']=={**parent_pool['inherited_public_reports'],**parent_reports}
parent_selected=parent_pool['selected']+[{'module':'TransferScalarChoiceCorrespondence01','source':parent_plan['targets'][0]['source'],'object':parent_events[-1]['result']['objects'][0]}]
assert len(parent_selected)==208 and len(pool['selected'])==208
for before,after in zip(parent_selected,pool['selected']):
 assert before['module']==after['module'] and before['source']==after['source'] and before['object']==after['object']
 assert pin(after['source']['path'])==after['source'] and pin(after['object']['path'])==after['object'] and pin(after['copy']['path'])==after['copy']
assert parent_plan['external_floor']==plan['external_floor']
reference={'parent':{'archive':pin(parent_archive),'manifest':pin(PARENT/'manifest.json'),'review':pin(PARENT/'review.json')},'ancestors':parent_review['inherited_reference'],'complete_owned_modules':208,'inherited_complete_reports':1473,'all_inherited_source_object_and_full_report_identities_verified':True,'scope':'Exact original208-module1473-report predecessor qualification. All original complete sealed histories remain referenced by full SHA; every shared source/object/report matches. No replay. Public-order branch remains independently retained.'}
dump(ROOT/'inherited-reference.json',reference)
records=[];payload=[]
def add(p,name,role):
 p=Path(p);assert name not in {n for n,_ in payload};payload.append((name,p.read_bytes()));records.append({'archive_path':name,'original':pin(p),'role':role})
for name in ['prepare.py','prepare_from02.py','execute_bounded.py','plan.json','review.json','source-mapping.json','events.jsonl']:
 add(CURRENT/name,'qualified/'+name,'exact successful qualification source and unchanged guards')
add(CURRENT/('handwritten/'+MODULE+'.lean'),'source/ShielddSecurity/'+MODULE+'.lean','handwritten complete source-shaped Nullifier codec theorem source')
add(stdout,'reports/fresh-10-complete-declarations.txt','original full theorem/definition types and allowed axiom audits')
add(plan['owned_import_pool']['path'],'context/owned-composition-review.json','exact qualified208-module first import root and1473 original reports; no object bytes')
add(ROOT/'inherited-reference.json','context/inherited-reference.json','full original sealed ancestor/history archive identities')
for name in ['manifest.json','review.json']:add(PARENT/name,'parent-qualification/'+name,'full original parent manifest and qualification review; all histories retained by sealed archive identity')
for row in pool['selected']:add(row['source']['path'],'source/imported/'+row['module']+'.lean','exact original qualified source, source identity matches original parent qualification')
for name in ['preservation_check.py','preservation.json']:add(CHECKPOINT/name,'preservation/'+name,'protected and foreign files, main status and clean exact runtime preserved')
mapping=json.loads((CURRENT/'source-mapping.json').read_bytes())
context=json.loads((CURRENT/'context/nullifier-field-codec-shape.json').read_bytes())
add(CURRENT/'context/nullifier-field-codec-shape.json','context/nullifier-field-codec-shape.json','exact alias/constructor/serializer source association; native semantics remain separate')
for key in ['canonical_domain','input_family_shape']:
 row=context[key];assert pin(row['path'])==row;add(row['path'],'context/'+Path(row['path']).name,'exact qualified source association; identity alone is not semantic correspondence')
for row in context['library_sources']:add(row['path'],'library/'+Path(row['path']).name,'exact locked registry alias and Scalar source')
runtime_base=Path('C:/src/shieldd-pr160-844389ee')
for row in context['runtime_sources']:
 assert pin(row['path'])==row;add(row['path'],'runtime/'+Path(row['path']).relative_to(runtime_base).as_posix(),'exact locked Fq alias, Nullifier and field encoding source')
add(DIAG.parent.parent/'shieldd.lock','context/shieldd.lock','exact full runtime commit')
for attempt in ['01','02']:
 failed=DIAG/('transfer-nullifier-field-codec-20261012-'+attempt)
 failed_event=json.loads((failed/'events.jsonl').read_text().splitlines()[-1]);assert failed_event['result']['status']=='failed'
 for p in sorted(failed.rglob('*')):
  if p.is_file():
   assert p.suffix not in ['.olean','.ilean','.c','.o'];assert pin(p) in plan['pins']
   add(p,'history/failed'+attempt+'/'+p.relative_to(failed).as_posix(),'exact failed dependent-if or empty-existential simplification and unused-simp reports; raw failures retained, no semantic negative control')
prior=DIAG/'transfer-nullifier-field-codec-endpoint-20261012-01'
assert not (prior/'manifest.json').exists()
add(prior/'assemble.py','history/unrun-assembly01/assemble.py','original unrun assembly prepared against earlier attempt; updated before sealing without proof replay')
add(ROOT/'prepare_assembly.py','prepare_assembly.py','exact fresh assembly derivation')
add(Path(__file__),'assemble.py','exact sealer source')
review={'status':'SOURCE_NULLIFIER_FIELD_CODEC_FULL_BYTE_LIST_DOMAIN_QUALIFIED','fresh_sources':1,'fresh_definition_audits':2,'fresh_structure_audits':0,'fresh_theorem_audits':8,'fresh_complete_public_audits':10,'fresh_audits':fresh,'inherited_complete_public_audits':1473,'inherited_reference':reference,'compiler_result':events[-1]['result'],'plan':pin(CURRENT/'plan.json'),'interfaces':mapping['interfaces'],'runtime_sha':mapping['runtime_sha'],'native_test_credit':0,'negative_control_credit':0,'rejected_attempts':2,'certification':False,'full_transfer':'OPEN','scope':mapping['scope']}
dump(ROOT/'review.json',review);add(ROOT/'review.json','review.json','full complete declarations and explicit native/full Transfer interfaces')
manifest={'schema':'transfer-nullifier-field-codec-endpoint-v1','entries':records,'fresh_audits':10,'inherited_audits':1473,'inherited_reference':reference,'object_bytes_in_archive':0,'toolchain_bytes_in_archive':0,'native_test_credit':0,'negative_control_credit':0,'certification':False,'scope':review['scope']}
dump(ROOT/'manifest.json',manifest);payload.append(('manifest.json',(ROOT/'manifest.json').read_bytes()))
with tarfile.open(archive,'w:xz',preset=6) as t:
 for name,raw in sorted(payload):
  info=tarfile.TarInfo(name);info.size=len(raw);info.mode=0o644;info.mtime=0;t.addfile(info,io.BytesIO(raw))
with tarfile.open(archive,'r:xz') as t:
 assert len(t.getmembers())==len(payload) and all(t.extractfile(name).read()==raw for name,raw in payload)
assert all(pin(r['original']['path'])==r['original'] for r in records)
print(json.dumps({'archive':pin(archive),'manifest':pin(ROOT/'manifest.json'),'review':pin(ROOT/'review.json'),'entries':len(records),'members':len(payload),'fresh_audits':10,'inherited_audits':1473,'native_test_credit':0,'certification':False}))
