from pathlib import Path
import hashlib, importlib.util, json, re, shutil
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
UP=DIAG/'transfer-scalar-ct-option-20261012-01'
POOL=DIAG/'transfer-scalar-additive-field-owned-floor-20261012-02'
MODULE='TransferScalarAdditiveField01'
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
target=plan['targets'][0];stdout=UP/'runs/01-TransferScalarCtOption01/stdout.txt'
current=m.audit(stdout.read_text(),target['audit_names']);assert len(current)==11 and current==ev[-1]['result']['audits']
assert pin(stdout)==ev[-1]['result']['stdout']
records=[(r['module'],r['source'],r['object']) for r in old['selected']]
records.append(('TransferScalarCtOption01',target['source'],ev[-1]['result']['objects'][0]))
audits=dict(old['inherited_public_reports']);assert set(audits).isdisjoint(current);audits.update(current)
assert len(records)==211 and len(audits)==1505
inputs=old['input_records']+[pin(UP/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','source-mapping.json','events.jsonl','execute_bounded.py','handwritten/TransferScalarCtOption01.lean','project/ShielddSecurity/TransferScalarCtOption01.lean']]+[pin(stdout),plan['owned_import_pool']]
inputs=list({json.dumps(r,sort_keys=True):r for r in inputs}.values())
POOL.mkdir();selected=[]
for name,source,obj in records:
 assert pin(source['path'])==source and pin(obj['path'])==obj
 copy=POOL/'modules/ShielddSecurity'/(name+'.olean');copy.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(obj['path'],copy)
 assert pin(copy)['sha256']==obj['sha256']
 selected.append({'module':name,'source':source,'object':obj,'copy':pin(copy)});inputs += [source,obj]
composition={'admission_ready':True,'kernel_credit':0,'objects':211,'selected':selected,'input_records':inputs,'inherited_public_reports':audits,'charged_new_object_bytes':sum(r['copy']['bytes'] for r in selected),'field_foundation':old['field_foundation'],'scope':'Exact qualified211-module1505-report predecessor closure reused without replay. Public-order branch remains independently retained. Source/object/report identity is checked; hashes are not semantic correspondence.'}
composition_file=POOL/'composition-review.json';dump(composition_file,composition)
handwritten=ROOT/'handwritten'/(MODULE+'.lean');source=handwritten.read_text();names=re.findall(r'^(?:structure|inductive|def|theorem) ([A-Za-z0-9_]+)',m.code_only(source),re.M)
assert len(names)==8 and re.findall(r'^#check @([^\n]+)',source,re.M)==names and re.findall(r'^#print axioms ([^\n]+)',source,re.M)==names
assert not re.search(r'\b(?:sorry|admit|axiom)\b',m.code_only(source))
project=ROOT/'project/ShielddSecurity'/handwritten.name;project.parent.mkdir(parents=True);shutil.copyfile(handwritten,project)
runtime=Path('C:/src/shieldd-pr160-844389ee');domain=json.loads((DIAG/'transfer-bounded-native-codec-20261011-02/context/canonical-domain.json').read_bytes())
for row in domain['runtime_sources']+domain['library_sources']:assert pin(row['path'])==row
lib=(runtime/'crates/crypto/primitives/src/lib.rs').read_text();nullifier=(runtime/'crates/core/component/sct/src/nullifier.rs').read_text();encoding=(runtime/'crates/crypto/primitives/src/encoding.rs').read_text()
assert 'pub use jubjub::{Fq, Fr, SubgroupPoint};' in lib
jubjub=next(r for r in domain['library_sources'] if 'jubjub' in r['path']);assert 'pub use bls12_381::Scalar as Fq;' in Path(jubjub['path']).read_text()
assert 'pub struct Nullifier(pub Fq);' in nullifier and 'let bytes: [u8; 32] = slice[..].try_into()?;' in nullifier and 'shieldd_sdk_crypto::encoding::field(&bytes)' in nullifier and 'self.0.to_bytes()' in nullifier
assert 'Option::from(Fq::from_bytes(bytes))' in encoding
scope='Eight complete source-model declarations derive exact mathematical field addition/subtraction/negation from qualified ADC/SBB/masked-addback/nonzero-mask word outputs. Three canonical operation wrappers obtain output widths/ranges from original source contracts. Two small symbolic lemmas derive subtraction by uniquely solving the canonical additive residue equation and removing Montgomery scaling. No desired mathematical output premise in operation theorems. Typed canonical inputs explicit. Compiler/native private origins/ABI/all native callers/full Transfer remain open.'
(ROOT/'context').mkdir();context=ROOT/'context/scalar-additive-field-shape.json'
dump(context,{'scope':scope,'exact_runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','runtime_sources':domain['runtime_sources'],'library_sources':domain['library_sources'],'alias_chain':['shieldd_sdk_crypto::Fq','jubjub::Fq','bls12_381::Scalar'],'not_jubjub_subgroup_scalar':True,'canonical_domain':pin(DIAG/'transfer-bounded-native-codec-20261011-02/context/canonical-domain.json'),'input_family_shape':pin(DIAG/'transfer-scalar-input-family-20261011-04/context/scalar-input-family-shape.json'),'native_binding_proved':False})
mapping=json.loads((UP/'source-mapping.json').read_bytes());mapping['scope']=scope;mapping['interfaces']=mapping['interfaces']+[scope];mapping['scalar_additive_field_source_shape']=pin(context)
mapping_file=ROOT/'source-mapping.json';dump(mapping_file,mapping)
plan['owned_import_pool']=pin(composition_file);plan['owned_imports']=[r['copy'] for r in selected]
plan['lean_path'][0:2]=[str(POOL/'modules'),str(ROOT/'project')]
plan['targets']=[{'module':MODULE,'source':pin(project),'predecessor_source':pin(handwritten),'imports':['ShielddSecurity.TransferScalarCtOption01'],'audit_names':['ShielddSecurity.'+MODULE+'.'+n for n in names]}]
plan['pins'] += inputs+plan['owned_imports']+[pin(p) for p in [Path(__file__),runner,handwritten,project,composition_file,mapping_file,context]]
plan['pins'] += domain['runtime_sources']+domain['library_sources']
plan['pins']=list({json.dumps(r,sort_keys=True):r for r in plan['pins']}.values())
plan['pins'] += [pin(ROOT/'prepare_recipe.py')]
subtle_context=json.loads((DIAG/'transfer-scalar-choice-masks-20261012-05/context/scalar-choice-masks-shape.json').read_bytes())
for key in ['subtle_locked_archive','subtle_source_copy','subtle_source_original','locked_cargo_manifest']:
 row=subtle_context[key];assert pin(row['path'])==row;plan['pins'].append(row)
raw=Path(subtle_context['subtle_source_copy']['path']).read_text()
assert 'if source.is_some().unwrap_u8() == 1u8 {' in raw and 'Option::Some(source.value)' in raw
assert 'pub struct CtOption<T>' in raw and 'pub fn new(value: T, is_some: Choice)' in raw
shape=json.loads(context.read_bytes());shape['subtle_source_context']=subtle_context
shape['subtle_source_shape']=pin(DIAG/'transfer-scalar-choice-masks-20261012-05/context/scalar-choice-masks-shape.json')
dump(context,shape);mapping['scalar_additive_field_source_shape']=pin(context);dump(mapping_file,mapping)
plan['pins']=[r for r in plan['pins'] if r['path'] not in [str(context),str(mapping_file)]]+[pin(context),pin(mapping_file),shape['subtle_source_shape']]
failed=DIAG/'transfer-scalar-additive-field-20261012-01'
assert json.loads((failed/'events.jsonl').read_text().splitlines()[-1])['result']['status']=='failed'
plan['pins'] += [pin(p) for p in sorted(failed.rglob('*')) if p.is_file()]+[pin(ROOT/'prepare_from01.py')]
plan['artifact_policy']='One handwritten narrow module and reports; exact211-module qualified first package root, no replay or runtime modification.'
plan['repairs']='All physical/thread/process/time/heartbeat/output/audit guards unchanged.'
plan['invocation']='Serial exact source-shaped nullifier codec; exact plan hash required.'
plan_file=ROOT/'plan.json';plan_file.write_bytes((json.dumps(plan,sort_keys=True,separators=(',',':'))+'\n').encode())
review={'status':'SCALAR_ADDITIVE_FIELD_SELF_REVIEWED_UNRUN','plan':pin(plan_file),'runner':pin(runner),'owned_floor':pin(composition_file),'fresh_audits':8,'inherited_audits':len(audits),'native_credit':0,'certification':False,'scope':scope}
dump(ROOT/'review.json',review)
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file())+6*8388608+1048576+262144<134217728
print(json.dumps(review))
