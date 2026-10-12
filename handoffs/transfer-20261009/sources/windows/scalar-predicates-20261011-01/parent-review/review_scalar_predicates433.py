from pathlib import Path
import json,hashlib,re,subprocess,tomllib,tarfile
J=Path(__file__).parent;W=J.parent;D=J/'windows-scalar-predicates-review01';P=D/'packet01';M='TransferScalarPredicates01';S=P/'source/ShielddSecurity'/(M+'.lean');s=S.read_text();R=W/'runtime-snapshot';LOCK='844389ee069e1fb2e576708842d0b389b4d9a44a'
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
a=json.loads((D/'endpoint-audit-review01.json').read_bytes());assert a['status']=='PASSED'and a['fresh_reports']==13
shape=json.loads((P/'context/scalar-predicates-shape.json').read_bytes());assert shape['exact_runtime_sha']==LOCK and shape['alias_chain']==['shieldd_sdk_crypto::Fq','jubjub::Fq','bls12_381::Scalar']and shape['native_binding_proved']is False and shape['not_jubjub_subgroup_scalar']is True
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

assert len(re.findall(r'^def ',s,re.M))==5 and len(re.findall(r'^theorem ',s,re.M))==8
scalar=(P/'library/bls12_381-0.8.0-scalar.rs').read_text();choice=subtlepaths['subtle_source_copy'].read_text()
for token in ['fn is_zero_vartime(&self) -> bool {\n        self.0 == Self::zero().0','Choice::from(self.to_bytes()[0] & 1)','bool::from(self.ct_eq(other))','self.0[0].ct_eq(&other.0[0])','& self.0[3].ct_eq(&other.0[3])']:assert token in scalar
assert 'fn from(source: Choice) -> bool {\n        debug_assert!((source.0 == 0u8) | (source.0 == 1u8));\n        source.0 != 0' in choice
assert all(pin(P/'context/original-choice-masks-shape.json')[k]==shape['subtle_source_shape'][k]for k in ['bytes','sha256'])
for token in ['def sourceChoiceBool (byte : UInt8) : Bool := decide (byte ≠ 0)','(valid : byte.toNat < 2)','def sourceScalarZeroVartimeBool (scalar : CanonicalScalar) : Bool :=\n  decide (scalar.words = sourceZero.words)','(serializerBytes scalar.words.toList).headD 0 &&& 1','canonical_internal_math_values_equal_iff_raw_words_equal','exact_source_scalar_equality_byte_derives_exact_raw_word_equality','fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value','source_scalar_odd_choice_byte_has_derived_bit_invariant scalar','first_typed_byte_low_bit_is_exact_little_endian_integer_parity (bytes : List UInt8)']:assert token in s
for name in ['source_scalar_equality_boolean_has_exact_mathematical_field_meaning','source_scalar_vartime_zero_boolean_has_exact_mathematical_field_meaning','source_scalar_odd_choice_byte_has_exact_mathematical_field_parity','source_scalar_odd_boolean_has_exact_mathematical_field_parity']:
 signature=re.search(r'theorem '+name+r'([\s\S]*?) := by',s).group(1)
 assert '(valid :'not in signature and '(desired'not in signature and '(expected'not in signature and '(corresponds :'not in signature
old=(P/'history/failed01/project/ShielddSecurity'/(M+'.lean')).read_text()
assert old.count('      rw [Nat.zero_mul]\n      rfl\n')==1
assert old.replace('      rw [Nat.zero_mul]\n      rfl\n','      rw [Nat.zero_mul]\n')==s
assert (P/'history/failed01/handwritten'/(M+'.lean')).read_text()==old
stdout=(P/'history/failed01/runs'/('01-'+M)/'stdout.txt').read_text();assert ':83:6: error: No goals to be solved' in stdout and stdout.count('error:')==1
records=[json.loads(x)for x in(P/'history/failed01/events.jsonl').read_text().splitlines()];assert len(records)==2 and records[1]['result']['status']=='failed'and records[1]['result']['reason']=='Lean exit 1'
review=json.loads((P/'review.json').read_text());assert review['rejected_attempts']==1 and review['fresh_definition_audits']==5 and review['fresh_theorem_audits']==8
assert sorted(x.name for x in(P/'history').iterdir())==['failed01','unrun-assembly01']
scope='Thirteen original complete source-model reports:five definitions/eight theorems. Exact locked Scalar equality/zero/is_odd and subtle Choice-to-bool source authenticated against clean runtime/Cargo-checksummed libraries. ALL canonical four-word values derive equality and zero mathematical meaning. ALL typed byte lists derive first-byte low-bit LE parity; fixed32-byte serializer yields field parity and its own Choice byte0/1 invariant. Equality producer derives byte0/1 for ALL four typed words; canonical equality and odd Boolean endpoints expose no validity/desired-output/correspondence premise. General arbitrary Choice conversion retains documented byte.toNat<2 contract explicitly; no validity inferred from Rust type. One original Lean exit1 redundant rfl failure retained; exact whole-source repair deletes only already-discharged trailing rfl, every declaration statement and source algorithm unchanged. One unrun assembly retained. Native indexing/compiler/volatile barrier/ABI/private caller origins/timing/full Transfer OPEN. Native3 UNRUN; final private/generated type/axiom census/exact-lock replay/atomic acceptance OPEN. Consumer2141527 is subset of Root2151534; unused PublicOrders7 remains preserved. No Root Lean replay.'
out=D/'semantic-source-review01.json';assert not out.exists();out.write_text(json.dumps(dict(status='PASSED_SOURCE_HISTORY',fresh_reports=13,source=pin(S),runtime_sha=LOCK,locked_library_archives=crate_pins+[pin(subtlepaths['subtle_locked_archive'])],failed_attempts=[dict(events=pin(P/'history/failed01/events.jsonl'),source=pin(P/'history/failed01/project/ShielddSecurity'/(M+'.lean')),stdout=pin(P/'history/failed01/runs'/('01-'+M)/'stdout.txt'))],scope=scope,native_execution='UNRUN',full_transfer='OPEN'),indent=2)+'\n');print('PASSED_SOURCE_HISTORY13 equality/zero/parity/Choice predicates; exact proof-only repair')
