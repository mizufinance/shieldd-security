from pathlib import Path
import json,hashlib,re,subprocess,tomllib,tarfile
J=Path(__file__).parent;W=J.parent;D=J/'windows-nullifier-field-domain-review01';P=D/'packet01';M='TransferNullifierFieldDomain01';S=P/'source/ShielddSecurity'/(M+'.lean');s=S.read_text();R=W/'runtime-snapshot';LOCK='844389ee069e1fb2e576708842d0b389b4d9a44a'
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
a=json.loads((D/'endpoint-audit-review01.json').read_bytes());assert a['status']=='PASSED'and a['fresh_reports']==11
shape=json.loads((P/'context/nullifier-field-domain-shape.json').read_bytes());assert shape['exact_runtime_sha']==LOCK and shape['alias_chain']==['shieldd_sdk_crypto::Fq','jubjub::Fq','bls12_381::Scalar']and shape['native_binding_proved']is False and shape['not_jubjub_subgroup_scalar']is True
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
assert len(re.findall(r'^def ',s,re.M))==3 and len(re.findall(r'^theorem ',s,re.M))==8
for token in ['(value : Fin nullifierModulus)','encodeLE 32 value.val','(Nat.lt_trans value.isLt (by decide : nullifierModulus < 256 ^ 32))','TransferScalarCanonicalDecoder01.byteDecoderPayload (canonicalResidueBytes value)','source_byte_decoder_payload_has_derived_range_and_serialized_value','sourceNullifierSliceDecode (canonicalResidueBytes value).toList = some (sourceResidueField value)','montgomeryValue (sourceResidueField value).words = value.val','sourceFieldResidue (sourceResidueField value) = value','sourceResidueField (sourceFieldResidue scalar) = scalar','canonical_internal_math_values_equal_iff_raw_words_equal','actual_source_decoder_covers_the_entire_legal_field_residue_domain','serializerBytes (sourceResidueField value).words.toList = (canonicalResidueBytes value).toList']:assert token in s
for token in ['(desired','(returned :','(accepted :','(prime :','(expected :']:assert token not in s
old=(P/'history/failed01/handwritten'/(M+'.lean')).read_text();assert old==(P/'history/failed01/project/ShielddSecurity'/(M+'.lean')).read_text()
x=old.replace('value.isLt.trans (by decide : nullifierModulus < 256 ^ 32)','Nat.lt_trans value.isLt (by decide : nullifierModulus < 256 ^ 32)').replace('    (sourceFieldResidue scalar).val = montgomeryValue scalar.words := by\n','    (sourceFieldResidue scalar).val = montgomeryValue scalar.words := by\n  dsimp only [sourceFieldResidue]\n');assert x==s
h=P/'history/failed01';events=[json.loads(l)for l in(h/'events.jsonl').read_text().splitlines()];assert len(events)==2 and events[-1]['result']['status']=='failed'and events[-1]['result']['reason']=='Lean exit 1';log=h/'runs/01-TransferNullifierFieldDomain01/stdout.txt';text=log.read_text();assert 'Invalid field `trans`'in text and 'maximum number of heartbeats (200000)'in text and 'sorryAx'in text
# All reports in a failed compiler stream remain rejected, including explicit sorryAx.
preps=[pin(p)for p in(P/'history/setup-failed-assembly01').rglob('*')if p.is_file()];assert preps and not list((P/'history/setup-failed-assembly01').rglob('events.jsonl'))
scope='Eleven complete original source-model reports:three definitions/eight theorems. Every Fin(p) residue is encoded into exact32 UInt8 little-endian bytes with decoded integer equal to that residue; actual modeled source R2 decoder payload derives its own canonical range, is accepted, has exact mathematical Montgomery field value and serializes back to original bytes. Source residue constructor and source serializer/math projection are mutual inverses on ALL canonical raw fields; no desired returned value/acceptance/range/prime conclusion supplied. Fin(p) and CanonicalScalar are explicit model domains, full field coverage is not restricted to UInt64 or a selected finite sample. Same exact locked runtime and checksummed Cargo crate source authentication as codec, Fq alias association separately authenticated; actual native private origins/slice/CtOption/compiler/ABI/callers/full Transfer trace OPEN, no subgroup Fr/timing claim. Original failed Lean-exit1 invalid trans/heartbeat200000 stream including sorryAx remains rejected and preserved. Repair only uses Nat.lt_trans and unfolds sourceFieldResidue before applying already accepted projection; all statements/algorithms other bytes identical and limits unchanged. Original failed assembly preparation retained, not a new verifier run.209modules1483reports consumer subset of Root2101490; preserve unused PublicOrders7 branch. No Root verifier replay, native controls/fullTransfer OPEN.'
out=D/'semantic-source-review01.json';assert not out.exists();out.write_text(json.dumps(dict(status='PASSED_SOURCE_HISTORY',fresh_reports=11,source=pin(S),runtime_sha=LOCK,locked_library_archives=crate_pins,failed_attempts=[dict(events=pin(h/'events.jsonl'),source=pin(h/'handwritten'/(M+'.lean')),stdout=pin(log))],failed_assembly_preparations=preps,scope=scope,native_execution='UNRUN',full_transfer='OPEN'),indent=2)+'\n');print('PASSED_SOURCE_HISTORY11 full modeled field-residue domain reports')
