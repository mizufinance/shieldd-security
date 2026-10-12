from pathlib import Path
import json,hashlib,re,subprocess,tomllib,tarfile
J=Path(__file__).parent;W=J.parent;D=J/'windows-scalar-input-semantics-review01';P=D/'packet01';M='TransferScalarInputSemantics01';S=P/'source/ShielddSecurity'/(M+'.lean');s=S.read_text();R=W/'runtime-snapshot';LOCK='844389ee069e1fb2e576708842d0b389b4d9a44a'
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
a=json.loads((D/'endpoint-audit-review01.json').read_bytes());assert a['status']=='PASSED'and a['fresh_reports']==7
shape=json.loads((P/'context/scalar-input-semantics-shape.json').read_bytes());assert shape['exact_runtime_sha']==LOCK and shape['alias_chain']==['shieldd_sdk_crypto::Fq','jubjub::Fq','bls12_381::Scalar']and shape['native_binding_proved']is False and shape['not_jubjub_subgroup_scalar']is True
for key,name in [('canonical_domain','canonical-domain.json'),('input_family_shape','scalar-input-family-shape.json')]:assert all(pin(P/'context'/name)[k]==shape[key][k]for k in ['bytes','sha256'])
assert subprocess.check_output(['git','-C',str(R),'rev-parse','HEAD'],text=True).strip()==LOCK
assert subprocess.check_output(['git','-C',str(R),'status','--porcelain'],text=True)==''
for v in shape['runtime_sources']:
 rel=v['path'].split('shieldd-pr160-844389ee\\',1)[1].replace('\\','/');p=P/'runtime'/rel
 assert all(pin(p)[k]==v[k]for k in ['bytes','sha256'])
 assert p.read_bytes()==subprocess.check_output(['git','-C',str(R),'show',LOCK+':'+rel])
lock=tomllib.loads((P/'runtime/Cargo.lock').read_text());registry=Path('/Users/antoinecyr/.cargo/registry')
crate_pins=[]
for crate,version,member,copy in [('jubjub','0.10.0','src/lib.rs','jubjub-0.10.0-lib.rs'),('bls12_381','0.8.0','src/scalar.rs','bls12_381-0.8.0-scalar.rs')]:
 locked=[p for p in lock['package']if p['name']==crate and p['version']==version];assert len(locked)==1
 archives=list(registry.glob('cache/*/'+crate+'-'+version+'.crate'));assert len(archives)==1;archive=archives[0];assert pin(archive)['sha256']==locked[0]['checksum']
 with tarfile.open(archive,'r:gz')as t:
  f=t.getmember(crate+'-'+version+'/'+member);assert f.isfile()and f.size<=1024*1024;data=t.extractfile(f).read()
 assert data==(P/'library'/copy).read_bytes();crate_pins.append(pin(archive))
for v in shape['library_sources']:
 p=P/'library'/v['path'].split('\\')[-1];assert all(pin(p)[k]==v[k]for k in ['bytes','sha256'])
assert 'pub use jubjub::{Fq, Fr, SubgroupPoint};'in(P/'runtime/crates/crypto/primitives/src/lib.rs').read_text()
assert 'pub use bls12_381::Scalar as Fq;'in(P/'library/jubjub-0.10.0-lib.rs').read_text()
assert 'Option::from(Fq::from_bytes(bytes))'in(P/'runtime/crates/crypto/primitives/src/encoding.rs').read_text()
null=(P/'runtime/crates/core/component/sct/src/nullifier.rs').read_text();assert 'encoding::field' in null and 'try_into()'in null
subtle=shape['subtle_source_context'];subtlepaths={}
for key,v in subtle.items():
 if isinstance(v,dict)and set(v)=={'path','bytes','sha256'}and key!='scalar_source':
  p=P/'library/subtle-authenticated'/key/v['path'].split('\\')[-1];assert all(pin(p)[k]==v[k]for k in ['bytes','sha256']);subtlepaths[key]=p
assert subtlepaths['locked_cargo_manifest'].read_bytes()==(P/'runtime/Cargo.lock').read_bytes()
locked=[x for x in lock['package']if x['name']=='subtle'and x['version']=='2.6.1'];assert len(locked)==1 and locked[0]['checksum']==pin(subtlepaths['subtle_locked_archive'])['sha256']
with tarfile.open(subtlepaths['subtle_locked_archive'],'r:gz')as t:assert t.extractfile('subtle-2.6.1/src/lib.rs').read()==subtlepaths['subtle_source_copy'].read_bytes()==subtlepaths['subtle_source_original'].read_bytes()
assert all(pin(P/'library/bls12_381-0.8.0-scalar.rs')[k]==subtle['scalar_source'][k]for k in ['bytes','sha256'])
assert len(re.findall(r'^def ',s,re.M))==1 and len(re.findall(r'^theorem ',s,re.M))==6
for token in ['def mathematicalInputEval : ScalarInputProgram → Option Nat','| .raw words => some (packWords words.toList % nullifierModulus)','| .wide bytes => some (decodeLE bytes.toList % nullifierModulus)','| .bytes bytes => if decodeLE bytes.toList < nullifierModulus then some (decodeLE bytes.toList) else none','| .add left right => do','| .sub left right => do','| .mul left right => do','| .neg value => do','| .double value => do','(program : ScalarInputProgram)','(sourceInputEval program).map (fun scalar : CanonicalScalar => montgomeryValue scalar.words) = mathematicalInputEval program','induction program with','actual_modeled_decoder_payload_serializer_returns_raw_modulus_value words','arbitrary_64_source_bytes_derive_canonical_field_and_exact_modular_key bytes','source_canonical_choice_byte_is_one_iff_parsed_integer_below_modulus','actual_modeled_canonical_multiply_has_exact_mathematical_field_value']:assert token in s
whole=re.search(r'theorem entire_represented_source_input_evaluator_has_exact_independent_mathematical_field_semantics([\s\S]*?) := by',s).group(1);assert whole.strip().startswith('(program : ScalarInputProgram) :')and whole.count('(program :')==1
for token in ['(desired','(expected :','(prime :','(accepted :','(corresponds :']:assert token not in whole
# Generic Option lifting lemmas expose their operation correspondence hypothesis;
# the whole theorem obtains each instance from independently accepted operations.
assert '(corresponds : ∀ a b,'in s and '(corresponds : ∀ a,'in s
finalplan=json.loads((P/'qualified/plan.json').read_bytes());history=[]
ops=[('sourceCanonicalAdd','(fun x y => (x + y) % nullifierModulus)'),('sourceCanonicalSub','(fun x y => (x + nullifierModulus - y) % nullifierModulus)'),('sourceCanonicalMul','(fun x y => (x * y) % nullifierModulus)')]
for label in ['failed01','failed03']:
 h=P/'history'/label;f=h/'handwritten'/(M+'.lean');old=f.read_text();assert old==(h/'project/ShielddSecurity'/(M+'.lean')).read_text();norm=old.replace('(fun scalar =>','(fun scalar : CanonicalScalar =>')
 norm=norm.replace('import ShielddSecurity.TransferScalarAdditiveField01\n','import ShielddSecurity.TransferScalarAdditiveField01\nimport ShielddSecurity.TransferScalarFieldValues01\n',1)
 for op,math in ops:norm=norm.replace('mapped_canonical_option_binary_operation_preserves_derived_field_semantics _ _ _ _','mapped_canonical_option_binary_operation_preserves_derived_field_semantics _ _ '+op+' '+math,1)
 norm=norm.replace('mapped_canonical_option_unary_operation_preserves_derived_field_semantics _ _ _','mapped_canonical_option_unary_operation_preserves_derived_field_semantics _ sourceCanonicalNeg (fun x => (nullifierModulus - x) % nullifierModulus)',1)
 norm=norm.replace('mapped_canonical_option_unary_operation_preserves_derived_field_semantics _ _ _','mapped_canonical_option_unary_operation_preserves_derived_field_semantics _ (fun a => sourceCanonicalAdd a a) (fun x => (x + x) % nullifierModulus)',1);assert norm==s
 originalplan=json.loads((h/'plan.json').read_bytes());assert originalplan['limits']==finalplan['limits']and originalplan['pressure_limits']==finalplan['pressure_limits']and(h/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes()
 events=[json.loads(l)for l in(h/'events.jsonl').read_text().splitlines()];assert len(events)==2 and events[-1]['result']['status']=='failed'and events[-1]['result']['reason']=='Lean exit 1';logs=list(h.rglob('stdout.txt'));assert len(logs)==1;text=logs[0].read_text()
 if label=='failed01':assert 'Invalid field notation' in text and 'cannot resolve field `words`'in text
 else:assert 'Application type mismatch' in text
 history.append(dict(source=pin(f),events=pin(h/'events.jsonl'),stdout=pin(logs[0]),failed_result=events[-1]['result'],scope='All failed-stream reports rejected; no partial qualification inferred.'))
preps=[]
for label in ['setup-failed02','unrun-assembly01','unrun-assembly02']:
 q=P/'history'/label;assert not list(q.rglob('events.jsonl'));files=[pin(p)for p in q.rglob('*')if p.is_file()];assert files;preps.append(dict(stage=label,files=files,scope='Preparation only; no verifier run/result inferred.'))
review=json.loads((P/'review.json').read_bytes());assert review['rejected_attempts']==2 and review['fresh_definition_audits']==1 and review['fresh_theorem_audits']==6
scope='Seven original complete source-model reports:one independent mathematicalInputEval definition/six theorems. Structural induction proves modeled sourceInputEval agrees with independent Option Nat residue semantics for EVERY ScalarInputProgram:raw4-word and wide64-byte constructors reduce actual decoded integer;32-byte constructor accepts iff canonical and yields that exact integer; add/sub/mul/neg/double compose mathematical values and propagate constructor refusal. No desired output/acceptance/operation-correspondence/prime hypothesis in the whole evaluator theorem. Two generic Option lifting lemmas explicitly have correspondence hypotheses, discharged internally by independently accepted operation proofs in all five arithmetic cases. Represented typed eight-constructor program family is explicit, not an exhaustive native caller/private constructor census. Exact clean844389ee runtime and checksummed jubjub/bls/subtle sources authenticated. Two original failed streams retained:untyped Option lambda field inference, then higher-order operator inference/missing direct multiplication import. Repairs add CanonicalScalar annotations, explicit operators and the qualified multiplication import; exact normalized whole source equality checked, no algorithm/desired-output/premise change. Illtyped original lambdas do not have a valid earlier kernel signature claimed. One setup count-check failure and two unrun assembly preparations retained separately, not verifier runs. Consumer2121513 is a subset of preserved Root2131520, PublicOrders7 retained. Compiler/ABI/private origins/native callers/3 native controls/full Transfer trace and final replay remain OPEN/UNRUN; no Root Lean replay.'
out=D/'semantic-source-review01.json';assert not out.exists();out.write_text(json.dumps(dict(status='PASSED_SOURCE_HISTORY',fresh_reports=7,source=pin(S),runtime_sha=LOCK,locked_library_archives=crate_pins+[pin(subtlepaths['subtle_locked_archive'])],failed_attempts=history,unrun_setup_and_assembly_preparations=preps,scope=scope,native_execution='UNRUN',full_transfer='OPEN'),indent=2)+'\n');print('PASSED_SOURCE_HISTORY7 entire represented input evaluator field/refusal semantics')
