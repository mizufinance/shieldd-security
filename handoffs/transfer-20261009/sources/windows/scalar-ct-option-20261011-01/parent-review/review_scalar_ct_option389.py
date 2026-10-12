from pathlib import Path
import json,hashlib,re,subprocess,tomllib,tarfile
J=Path(__file__).parent;W=J.parent;D=J/'windows-scalar-ct-option-review01';P=D/'packet01';M='TransferScalarCtOption01';S=P/'source/ShielddSecurity'/(M+'.lean');s=S.read_text();R=W/'runtime-snapshot';LOCK='844389ee069e1fb2e576708842d0b389b4d9a44a'
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
a=json.loads((D/'endpoint-audit-review01.json').read_bytes());assert a['status']=='PASSED'and a['fresh_reports']==11
shape=json.loads((P/'context/scalar-ct-option-shape.json').read_bytes());assert shape['exact_runtime_sha']==LOCK and shape['alias_chain']==['shieldd_sdk_crypto::Fq','jubjub::Fq','bls12_381::Scalar']and shape['native_binding_proved']is False and shape['not_jubjub_subgroup_scalar']is True
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
rust=subtlepaths['subtle_source_copy'].read_text()
for token in ['pub fn new(value: T, is_some: Choice) -> CtOption<T>','value: value,','is_some: is_some,','pub fn is_some(&self) -> Choice {\n        self.is_some','pub fn unwrap_u8(&self) -> u8 {\n        self.0','if source.is_some().unwrap_u8() == 1u8 {\n            Option::Some(source.value)\n        } else {\n            None']:assert token in rust
for token in ['let is_some = (borrow as u8) & 1;','tmp *= &R2;','CtOption::new(tmp, Choice::from(is_some))']:assert token in (P/'library/bls12_381-0.8.0-scalar.rs').read_text()
assert len(re.findall(r'^def ',s,re.M))==3 and len(re.findall(r'^theorem ',s,re.M))==7 and len(re.findall(r'^structure ',s,re.M))==1
for token in ['structure SourceCtOption (α : Type)','isSomeByte : UInt8','if source.isSomeByte = 1 then some source.value else none','sourceCtOptionIntoOption source = some value ↔ source.isSomeByte = 1 ∧ source.value = value','(bytes : Vector UInt8 32)','sourceCtOptionNew (byteDecoderPayload bytes) (sourceCanonicalChoiceByte bytes)','sourceCtOptionIntoOption (sourceByteDecoderCtOption bytes) = sourceDecodeOption bytes','(sourceByteDecoderCtOption bytes).isSomeByte.toNat < 2','packWords (sourceByteDecoderCtOption bytes).value.toList < nullifierModulus','montgomeryValue (sourceByteDecoderCtOption bytes).value = decodeLE bytes.toList % nullifierModulus','(refused : ¬ decodeLE bytes.toList < nullifierModulus)','(sourceByteDecoderCtOption bytes).value = byteDecoderPayload bytes','(sourceByteDecoderCtOption bytes).isSomeByte = 0']:assert token in s
for token in ['(desired','(validByte :','(canonical :','(prime :','(expected :','(payload :']:assert token not in s
review=json.loads((P/'review.json').read_bytes());assert review['rejected_attempts']==0 and review['fresh_structure_audits']==1 and review['fresh_theorem_audits']==7 and review['fresh_definition_audits']==3
assert not list((P/'history').rglob('events.jsonl'))
scope='Eleven original complete source-model reports:one structure,three definitions,seven theorems. Authenticated exact locked subtle2.6.1 CtOption::new retains payload/Choice byte, projections return stored fields, From conversion returns Some(exact payload) iff stored byte1; conversion theorem covers every byte without a caller-validity premise. Actual modeled32-byte Scalar constructor derives its own byte0/1 invariant, canonical stored R2 payload, modular Montgomery meaning and exact acceptance for all inputs; refused constructor still retains actual canonical payload and byte0. Arbitrary typed UInt8 vector domain, no desired value/range/prime/conclusion premise. Exact clean runtime844389ee and Cargo-checksummed jubjub/bls/subtle sources independently authenticated. Rust Choice documented general input0/1 contract not inferred from raw type; source byte constructor derives it. Model/source association does not prove compiler/layout/volatile barriers/ABI/eager effects/timing/private origins/all native callers/full Transfer. Constructor/recursor/private generated final census separately OPEN. No failed original CtOption proof attempt reported; no Root replay. Consumer2101494 is a subset of Root2111501, PublicOrders7 preserved. Native3 UNRUN/full Transfer OPEN.'
out=D/'semantic-source-review01.json';assert not out.exists();out.write_text(json.dumps(dict(status='PASSED_SOURCE_HISTORY',fresh_reports=11,source=pin(S),runtime_sha=LOCK,locked_library_archives=crate_pins+[pin(subtlepaths['subtle_locked_archive'])],failed_attempts=[],scope=scope,native_execution='UNRUN',full_transfer='OPEN'),indent=2)+'\n');print('PASSED_SOURCE_HISTORY11 exact modeled CtOption stored payload and conversion reports')
