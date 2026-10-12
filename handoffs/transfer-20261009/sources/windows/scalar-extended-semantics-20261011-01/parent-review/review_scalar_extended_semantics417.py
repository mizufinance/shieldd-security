from pathlib import Path
import json,hashlib,re,subprocess,tomllib,tarfile
J=Path(__file__).parent;W=J.parent;D=J/'windows-scalar-extended-semantics-review01';P=D/'packet01';M='TransferScalarExtendedSemantics01';S=P/'source/ShielddSecurity'/(M+'.lean');s=S.read_text();R=W/'runtime-snapshot';LOCK='844389ee069e1fb2e576708842d0b389b4d9a44a'
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
a=json.loads((D/'endpoint-audit-review01.json').read_bytes());assert a['status']=='PASSED'and a['fresh_reports']==7
shape=json.loads((P/'context/scalar-extended-semantics-shape.json').read_bytes());assert shape['exact_runtime_sha']==LOCK and shape['alias_chain']==['shieldd_sdk_crypto::Fq','jubjub::Fq','bls12_381::Scalar']and shape['native_binding_proved']is False and shape['not_jubjub_subgroup_scalar']is True
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
assert len(re.findall(r'^def ',s,re.M))==2 and len(re.findall(r'^theorem ',s,re.M))==5
pool=json.loads((J/'windows-reviewed-ancestry-pool1527-reports214-modules01.json').read_bytes());family=Path(pool['modules']['TransferScalarExtendedFamily01']['local_reviewed_source']).read_text()
ctors=re.findall(r'^  \| (\w+)',family.split('inductive ScalarExtendedProgram where\n',1)[1].split('\ndef sourceExtendedEval',1)[0],re.M)
mathbody=s.split('def mathematicalExtendedEval : ScalarExtendedProgram → Option Nat\n',1)[1].split('\ntheorem entire_represented_extended',1)[0];mathctors=re.findall(r'^  \| \.(\w+)',mathbody,re.M)
assert ctors==mathctors==['input','constant','zero','one','fromU64','randomBytes','add','sub','mul','neg','double','square','pow','powVartime','invert','select']
expected_constant='''def mathematicalPublicConstant : PublicConstant → Nat
  | .twoInverse => (nullifierModulus + 1) / 2
  | .generator => 7
  | .rootOfUnity => 10238227357739495823651030575849232062558860180284477541189508159991286009131
  | .rootOfUnityInverse => 2361660012179324004544952053205906600198439069793331036989202475535180077688
  | .delta => 3793952369011177517951424454785176000433849974408744014172535497121832470999''';assert expected_constant in s
for token in ['cases constant <;> decide','(sourceInvert scalar).map (fun value : CanonicalScalar => montgomeryValue value.words)','if montgomeryValue scalar.words = 0 then none','exact_source_invert_chain_derives_successful_canonical_payload scalar','exact_source_invert_payload_has_modulus_minus_two_field_power scalar payload returned','some value.toNat','Nat.lt_trans value.toNat_lt (by decide : UInt64.size < nullifierModulus)','entire_represented_source_input_evaluator_has_exact_independent_mathematical_field_semantics program','exact_source_constant_time_pow_has_mathematical_little_endian_field_power a exponent','exact_source_variable_time_pow_has_mathematical_little_endian_field_power a exponent','actual_modeled_canonical_optimized_square_has_exact_mathematical_field_value','(fun x => if x = 0 then none else some (x ^ (nullifierModulus - 2) % nullifierModulus))','pure (if choice then b else a)']:assert token in s
select=mathbody.split('| .select choice first second => do\n',1)[1];assert 'let a ← mathematicalExtendedEval first; let b ← mathematicalExtendedEval second' in select
whole=re.search(r'theorem entire_represented_extended_source_evaluator_has_exact_independent_field_and_refusal_semantics([\s\S]*?) := by',s).group(1);assert whole.strip().startswith('(program : ScalarExtendedProgram) :')
for token in ['(desired','(expected :','(prime :','(accepted :','(corresponds :','(returned :']:assert token not in whole
invert=re.search(r'theorem source_inversion_has_exact_mathematical_power_and_zero_refusal_semantics([\s\S]*?) := by',s).group(1);assert invert.strip().startswith('(scalar : CanonicalScalar) :')and '(returned :'not in invert
assert '(corresponds : ∀ a,'in s
review=json.loads((P/'review.json').read_bytes());assert review['rejected_attempts']==0 and review['fresh_definition_audits']==2 and review['fresh_theorem_audits']==5 and not list((P/'history').rglob('events.jsonl'))
scope='Seven original complete source-model reports:two independent mathematical definitions/five theorems. Constructor census matches ALL16 represented ScalarExtendedProgram constructors. Structural induction composes independent input semantics, five separately stated public integer constants, zero/one, exact UInt64 construction,64-byte integer residue, add/sub/mul/neg/double/optimized square, both little-endian exponent loops, inversion exponentp−2 and exact zero refusal, and eager Boolean selection. Both branches of selection are evaluated in source/model semantics and refusals propagate, even from the unselected branch. Inversion obtains canonical payload/chain result internally; no desired output/acceptance/prime/correspondence/returned-payload hypothesis in the whole evaluator or inversion theorem. Generic partial-Option lifting correspondence hypothesis explicitly discharged by accepted inversion theorem. Complete16-constructor represented model domain and return/failure projection only: RNG distribution/eager side effects/compiler/ABI/native caller/private origin census/full Transfer OPEN. Five public constants are mathematical values, no new order/generator certification inferred; unused independently accepted PublicOrders7 remains in preserved union. Exact clean844389ee runtime/Cargo-checksummed jubjub/bls/subtle source association authenticated. No original failed proof attempt reported; no Root Lean replay. Consumer2131520 is subset of Root2141527. Native3 controls and final private/generated type/axiom census/full exact-lock replay/atomic acceptance remain OPEN/UNRUN.'
out=D/'semantic-source-review01.json';assert not out.exists();out.write_text(json.dumps(dict(status='PASSED_SOURCE_HISTORY',fresh_reports=7,source=pin(S),runtime_sha=LOCK,locked_library_archives=crate_pins+[pin(subtlepaths['subtle_locked_archive'])],represented_constructor_census=ctors,failed_attempts=[],scope=scope,native_execution='UNRUN',full_transfer='OPEN'),indent=2)+'\n');print('PASSED_SOURCE_HISTORY7 complete16-constructor represented extended field/refusal semantics')
