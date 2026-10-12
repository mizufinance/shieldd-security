from pathlib import Path
import hashlib, importlib.util, json, re, shutil
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
UP=DIAG/'transfer-scalar-choice-correspondence-20261012-01'
POOL=DIAG/'transfer-nullifier-field-codec-owned-floor-20261012-01'
MODULE='TransferNullifierFieldCodec01'
def pin(p):
 p=Path(p);b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def dump(p,o):p.write_bytes((json.dumps(o,indent=2,sort_keys=True)+'\n').encode())
assert not (ROOT/'plan.json').exists() and not POOL.exists()
runner=ROOT/'execute_bounded.py';shutil.copyfile(UP/runner.name,runner)
assert pin(runner)['sha256']=='7237060ba9e0d0b98e93cfe5aceb86a4d7390e2af2471b43e39cf3750ebc642b'
spec=importlib.util.spec_from_file_location('codec_auditor',runner);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
plan=json.loads((UP/'plan.json').read_bytes());old=json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
ev=[json.loads(x) for x in (UP/'events.jsonl').read_text().splitlines()]
assert len(ev)==2 and ev[-1]['result']['status']=='passed'
target=plan['targets'][0];stdout=UP/'runs/01-TransferScalarChoiceCorrespondence01/stdout.txt'
current=m.audit(stdout.read_text(),target['audit_names']);assert len(current)==6 and current==ev[-1]['result']['audits']
assert pin(stdout)==ev[-1]['result']['stdout']
records=[(r['module'],r['source'],r['object']) for r in old['selected']]
records.append(('TransferScalarChoiceCorrespondence01',target['source'],ev[-1]['result']['objects'][0]))
audits=dict(old['inherited_public_reports']);assert set(audits).isdisjoint(current);audits.update(current)
assert len(records)==208 and len(audits)==1473
inputs=old['input_records']+[pin(UP/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','source-mapping.json','events.jsonl','execute_bounded.py','handwritten/TransferScalarChoiceCorrespondence01.lean','project/ShielddSecurity/TransferScalarChoiceCorrespondence01.lean']]+[pin(stdout),plan['owned_import_pool']]
inputs=list({json.dumps(r,sort_keys=True):r for r in inputs}.values())
POOL.mkdir();selected=[]
for name,source,obj in records:
 assert pin(source['path'])==source and pin(obj['path'])==obj
 copy=POOL/'modules/ShielddSecurity'/(name+'.olean');copy.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(obj['path'],copy)
 assert pin(copy)['sha256']==obj['sha256']
 selected.append({'module':name,'source':source,'object':obj,'copy':pin(copy)});inputs += [source,obj]
composition={'admission_ready':True,'kernel_credit':0,'objects':208,'selected':selected,'input_records':inputs,'inherited_public_reports':audits,'charged_new_object_bytes':sum(r['copy']['bytes'] for r in selected),'field_foundation':old['field_foundation'],'scope':'Exact qualified208-module1473-report predecessor closure reused without replay. Public-order branch remains independently retained. Source/object/report identity is checked; hashes are not semantic correspondence.'}
composition_file=POOL/'composition-review.json';dump(composition_file,composition)
handwritten=ROOT/'handwritten'/(MODULE+'.lean');source=handwritten.read_text();names=re.findall(r'^(?:structure|inductive|def|theorem) ([A-Za-z0-9_]+)',m.code_only(source),re.M)
assert len(names)==10 and re.findall(r'^#check @([^\n]+)',source,re.M)==names and re.findall(r'^#print axioms ([^\n]+)',source,re.M)==names
assert not re.search(r'\b(?:sorry|admit|axiom)\b',m.code_only(source))
project=ROOT/'project/ShielddSecurity'/handwritten.name;project.parent.mkdir(parents=True);shutil.copyfile(handwritten,project)
runtime=Path('C:/src/shieldd-pr160-844389ee');domain=json.loads((DIAG/'transfer-bounded-native-codec-20261011-02/context/canonical-domain.json').read_bytes())
for row in domain['runtime_sources']+domain['library_sources']:assert pin(row['path'])==row
lib=(runtime/'crates/crypto/primitives/src/lib.rs').read_text();nullifier=(runtime/'crates/core/component/sct/src/nullifier.rs').read_text();encoding=(runtime/'crates/crypto/primitives/src/encoding.rs').read_text()
assert 'pub use jubjub::{Fq, Fr, SubgroupPoint};' in lib
jubjub=next(r for r in domain['library_sources'] if 'jubjub' in r['path']);assert 'pub use bls12_381::Scalar as Fq;' in Path(jubjub['path']).read_text()
assert 'pub struct Nullifier(pub Fq);' in nullifier and 'let bytes: [u8; 32] = slice[..].try_into()?;' in nullifier and 'shieldd_sdk_crypto::encoding::field(&bytes)' in nullifier and 'self.0.to_bytes()' in nullifier
assert 'Option::from(Fq::from_bytes(bytes))' in encoding
scope='Ten source-model declarations cover all typed byte lists for the exact source-shaped Nullifier slice constructor. Success iff length32 and integer below BLS Scalar modulus; returned field meaning equals the input integer and serialized bytes equal input. Every canonical source field encodes and decodes back to the same raw field; accepted decoding is injective and wrong lengths refuse. Exact runtime Fq->jubjub::Fq->bls12_381::Scalar alias/source association is recorded separately, not proved by hashes. Slice/Option/CtOption/compiler/native ABI/private constructor origins/all native caller binding/full Transfer remain open. Returned success projection only; no timing or eager-computation claim.'
(ROOT/'context').mkdir();context=ROOT/'context/nullifier-field-codec-shape.json'
dump(context,{'scope':scope,'exact_runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','runtime_sources':domain['runtime_sources'],'library_sources':domain['library_sources'],'alias_chain':['shieldd_sdk_crypto::Fq','jubjub::Fq','bls12_381::Scalar'],'not_jubjub_subgroup_scalar':True,'canonical_domain':pin(DIAG/'transfer-bounded-native-codec-20261011-02/context/canonical-domain.json'),'input_family_shape':pin(DIAG/'transfer-scalar-input-family-20261011-04/context/scalar-input-family-shape.json'),'native_binding_proved':False})
mapping=json.loads((UP/'source-mapping.json').read_bytes());mapping['scope']=scope;mapping['interfaces']=mapping['interfaces']+[scope];mapping['nullifier_field_codec_source_shape']=pin(context)
mapping_file=ROOT/'source-mapping.json';dump(mapping_file,mapping)
plan['owned_import_pool']=pin(composition_file);plan['owned_imports']=[r['copy'] for r in selected]
plan['lean_path'][0:2]=[str(POOL/'modules'),str(ROOT/'project')]
plan['targets']=[{'module':MODULE,'source':pin(project),'predecessor_source':pin(handwritten),'imports':['ShielddSecurity.TransferScalarInputFamily01','ShielddSecurity.TransferScalarChoiceMasks01'],'audit_names':['ShielddSecurity.'+MODULE+'.'+n for n in names]}]
plan['pins'] += inputs+plan['owned_imports']+[pin(p) for p in [Path(__file__),runner,handwritten,project,composition_file,mapping_file,context]]
plan['pins'] += domain['runtime_sources']+domain['library_sources']
plan['pins']=list({json.dumps(r,sort_keys=True):r for r in plan['pins']}.values())
plan['artifact_policy']='One handwritten narrow module and reports; exact208-module qualified first package root, no replay or runtime modification.'
plan['repairs']='All physical/thread/process/time/heartbeat/output/audit guards unchanged.'
plan['invocation']='Serial exact source-shaped nullifier codec; exact plan hash required.'
plan_file=ROOT/'plan.json';plan_file.write_bytes((json.dumps(plan,sort_keys=True,separators=(',',':'))+'\n').encode())
review={'status':'NULLIFIER_FIELD_CODEC_SELF_REVIEWED_UNRUN','plan':pin(plan_file),'runner':pin(runner),'owned_floor':pin(composition_file),'fresh_audits':10,'inherited_audits':len(audits),'native_credit':0,'certification':False,'scope':scope}
dump(ROOT/'review.json',review)
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file())+6*8388608+1048576+262144<134217728
print(json.dumps(review))
