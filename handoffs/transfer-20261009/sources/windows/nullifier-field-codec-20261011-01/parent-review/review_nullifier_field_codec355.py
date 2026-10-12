from pathlib import Path
import json,hashlib,re,subprocess,tomllib,tarfile
J=Path(__file__).parent;W=J.parent;D=J/'windows-nullifier-field-codec-review01';P=D/'packet01';M='TransferNullifierFieldCodec01';S=P/'source/ShielddSecurity'/(M+'.lean');s=S.read_text();R=W/'runtime-snapshot';LOCK='844389ee069e1fb2e576708842d0b389b4d9a44a'
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
a=json.loads((D/'endpoint-audit-review01.json').read_bytes());assert a['status']=='PASSED'and a['fresh_reports']==10
shape=json.loads((P/'context/nullifier-field-codec-shape.json').read_bytes());assert shape['exact_runtime_sha']==LOCK and shape['alias_chain']==['shieldd_sdk_crypto::Fq','jubjub::Fq','bls12_381::Scalar']and shape['native_binding_proved']is False and shape['not_jubjub_subgroup_scalar']is True
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
assert len(re.findall(r'^def ',s,re.M))==2 and len(re.findall(r'^theorem ',s,re.M))==8
for token in ['if width : bytes.length = 32 then','else none','bytes.length = 32 ∧ decodeLE bytes < nullifierModulus','montgomeryValue scalar.words = decodeLE bytes ∧','serializerBytes scalar.words.toList = bytes','sourceNullifierSliceDecode (sourceNullifierEncode scalar).toList = some scalar','(bytes : List UInt8)','(scalar : CanonicalScalar)','(wrongWidth : bytes.length ≠ 32)']:assert token in s
for token in ['(desired','(acceptedFlag','(prime :','(fieldMeaning :','(canonicalInput :']:assert token not in s
# Byte-exact proof-only corrections; all contracts and algorithms stay identical.
old1=(P/'history/failed01/handwritten'/(M+'.lean')).read_text();old2=(P/'history/failed02/handwritten'/(M+'.lean')).read_text()
for name,old in [('failed01',old1),('failed02',old2)]:assert old==(P/'history'/name/'project/ShielddSecurity'/(M+'.lean')).read_text()
branch="    constructor\n    · rintro ⟨scalar, impossible⟩; exact impossible\n    · intro impossible; exact False.elim impossible\n"
x=old2.replace('simp only [reduceCtorEq, exists_const, width, false_and]\n','simp only [reduceCtorEq, width, false_and]\n'+branch);assert x==s
x=old1.replace('Vector.toList, List.toList_toArray','Vector.toList').replace('  · simp only [sourceNullifierSliceDecode, dif_neg width, reduceCtorEq, exists_const,\n      width, false_and]\n','  · rw [sourceNullifierSliceDecode, dif_neg width]\n    simp only [reduceCtorEq, width, false_and]\n'+branch);assert x==s
history=[]
for name in ['failed01','failed02']:
 h=P/'history'/name;events=[json.loads(l)for l in(h/'events.jsonl').read_text().splitlines()];assert len(events)==2 and events[-1]['result']['status']=='failed'and events[-1]['result']['reason']=='Lean exit 1'
 log=h/'runs/01-TransferNullifierFieldCodec01/stdout.txt';text=log.read_text();assert 'error: unsolved goals'in text and 'unused' in text
 history.append(dict(events=pin(h/'events.jsonl'),source=pin(h/'handwritten'/(M+'.lean')),stdout=pin(log)))
assembly=[pin(p)for p in(P/'history/unrun-assembly01').rglob('*')if p.is_file()];assert len(assembly)==1
scope='Ten complete original source-model reports:two definitions/eight theorems. For every typed byte list, modeled Nullifier slice constructor succeeds iff exact length32 and LE integer below BLS Scalar modulus; no supplied width/canonicality/desired field conclusion. Successful returned CanonicalScalar has mathematical Montgomery value exactly input integer and serializes to original bytes. Every canonical raw source field encodes and decodes to identical CanonicalScalar; accepted byte-list decoding injective and all other lengths refuse. Root authenticates exact runtime files against clean full locked Git SHA and jubjub0.10.0/bls12_3810.8.0 library source against Cargo.lock checksummed local crate archives; actual Fq->jubjub::Fq->bls12_381::Scalar alias association (not subgroup Fr) is source identity, not a proof of native execution. CanonicalScalar remains explicit model domain. Slice/Option/CtOption/compiler/native ABI/private constructor origins/all native caller binding/full native Transfer trace OPEN. Returned success value only; eager effects/timing not certified. Both original Lean-exit1/unsolved-goal/unused-simp histories retained; only proof-body rewrites/simplification change, all contracts/algorithms byte-identical after explicit repairs. One original unrun assembly file preserved.208modules1473reports actual consuming closure is subset of Root2091480; preserve unused PublicOrders7. Physical guard unchanged, no Root verifier replay. Native controls/fullTransfer OPEN.'
out=D/'semantic-source-review01.json';assert not out.exists();out.write_text(json.dumps(dict(status='PASSED_SOURCE_HISTORY',fresh_reports=10,source=pin(S),runtime_sha=LOCK,locked_library_archives=crate_pins,failed_attempts=history,unrun_assembly_preparations=assembly,scope=scope,native_execution='UNRUN',full_transfer='OPEN'),indent=2)+'\n');print('PASSED_SOURCE_HISTORY10 exact full-domain modeled codec reports')
