from pathlib import Path
import json,hashlib,re,subprocess,tomllib,tarfile
J=Path(__file__).parent;W=J.parent;D=J/'windows-scalar-additive-field-review01';P=D/'packet01';M='TransferScalarAdditiveField01';S=P/'source/ShielddSecurity'/(M+'.lean');s=S.read_text();R=W/'runtime-snapshot';LOCK='844389ee069e1fb2e576708842d0b389b4d9a44a'
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
a=json.loads((D/'endpoint-audit-review01.json').read_bytes());assert a['status']=='PASSED'and a['fresh_reports']==8
shape=json.loads((P/'context/scalar-additive-field-shape.json').read_bytes());assert shape['exact_runtime_sha']==LOCK and shape['alias_chain']==['shieldd_sdk_crypto::Fq','jubjub::Fq','bls12_381::Scalar']and shape['native_binding_proved']is False and shape['not_jubjub_subgroup_scalar']is True
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
assert len(re.findall(r'^def ',s,re.M))==3 and len(re.findall(r'^theorem ',s,re.M))==5
for token in ['(left right : CanonicalScalar)','(scalar : CanonicalScalar)','(relation : (output + right) % nullifierModulus = left)','(rawContract : output = (left + nullifierModulus - right) % nullifierModulus)','source_four_adc_and_modulus_sub_preserve_canonical_modular_sum','source_four_sbb_and_masked_adc_retain_four_output_limbs','canonical_operands_source_subtraction_has_exact_canonical_modular_value','source_four_sbb_and_nonzero_mask_derive_canonical_negation','certifyResult','left.canonical right.canonical contract.2','montgomeryValue (sourceCanonicalAdd left right).words','montgomeryValue (sourceCanonicalSub left right).words','montgomeryValue (sourceCanonicalNeg scalar).words','scalar.canonical raw']:assert token in s
for token in ['(desired','(expected :','(prime :','(accepted :']:assert token not in s
# Supporting raw algebraic lemma has an explicit raw difference contract; each
# canonical operation theorem obtains that contract from the accepted modeled
# ADC/SBB/mask algorithm and exposes no desired output premise.
for name in ['actual_source_canonical_add_has_exact_mathematical_field_sum','actual_source_canonical_sub_has_exact_mathematical_field_difference','actual_source_canonical_negation_has_exact_mathematical_field_value']:
 match=re.search(r'theorem '+name+r'([\s\S]*?) := by',s);assert match and 'Contract'not in match.group(1)and 'Range'not in match.group(1)
old=(P/'history/rejected01/handwritten'/(M+'.lean')).read_text();assert old==(P/'history/rejected01/project/ShielddSecurity'/(M+'.lean')).read_text()
norm=old.replace('    (left right output : Nat) (leftRange : left < nullifierModulus)\n','    (left right output : Nat)\n',1).replace('    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) scaled','    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) scaled',1);assert norm==s
h=P/'history/rejected01';events=[json.loads(l)for l in(h/'events.jsonl').read_text().splitlines()];assert len(events)==2 and events[-1]['result']['status']=='failed'and events[-1]['result']['reason']=='Lean error/placeholder output'
log=h/'runs/01-TransferScalarAdditiveField01/stdout.txt';text=log.read_text();assert 'warning: unused variable `leftRange`'in text and 'sorryAx'not in text
originalplan=json.loads((h/'plan.json').read_bytes());finalplan=json.loads((P/'qualified/plan.json').read_bytes());assert originalplan['limits']==finalplan['limits']and originalplan['pressure_limits']==finalplan['pressure_limits']and(h/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes()
scope='Eight complete original source-model reports:three definitions/five theorems. Canonical add/sub/neg wrappers derive their own output width/range from accepted modeled ADC/SBB/masked-addback/nonzero-mask word algorithms; output Montgomery mathematical values equal modular sum/difference/negation for all CanonicalScalar inputs. Supporting generic algebraic lemmas have explicit residue/raw difference relations; operation theorems derive those relations internally and have no desired output/range/prime premise. Raw-word canonical input domain remains explicit. Exact clean runtime844389ee and checksummed Cargo library sources authenticated, including subtle2.6.1; SDK Fq alias is jubjubFq/blsScalar, not subgroupFr. One original compiled warning stream was rejected by the audit and retained; repair removes only the unused leftRange premise of the generic lemma and its corresponding internal argument, strengthening that lemma. All remaining source bytes/algorithms and physical guards identical. Actual compiler/private constructors/ABI/native callers/full trace and3 native controls OPEN/UNRUN. Consumer211modules1505reports is a subset of Root preserved union after CtOption acceptance; retain PublicOrders7. No Root Lean replay/full Transfer closure.'
out=D/'semantic-source-review01.json';assert not out.exists();out.write_text(json.dumps(dict(status='PASSED_SOURCE_HISTORY',fresh_reports=8,source=pin(S),runtime_sha=LOCK,locked_library_archives=crate_pins+[pin(subtlepaths['subtle_locked_archive'])],failed_attempts=[dict(events=pin(h/'events.jsonl'),source=pin(h/'handwritten'/(M+'.lean')),stdout=pin(log))],scope=scope,native_execution='UNRUN',full_transfer='OPEN'),indent=2)+'\n');print('PASSED_SOURCE_HISTORY8 modeled additive field reports')
