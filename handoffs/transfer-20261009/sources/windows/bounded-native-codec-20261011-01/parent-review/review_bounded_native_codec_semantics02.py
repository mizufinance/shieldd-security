"""Independent native domain and scoped model review; no verifier launch."""
from pathlib import Path
import ast, hashlib, json, re, tarfile, tomllib
J=Path(__file__).parent;W=J.parent;P=J/'windows-bounded-native-codec-review02/packet01'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=sha(b))
read=lambda p:json.loads(p.read_bytes())
domain=read(P/'qualified/context/canonical-domain.json')
lock=tomllib.loads((P/'runtime/Cargo.lock').read_text())
assert (P/'runtime/Cargo.lock').read_bytes()==(W/'runtime-snapshot/Cargo.lock').read_bytes()
cache=Path('/Users/antoinecyr/.cargo/registry');library=[]
for name,relative in [('jubjub','src/lib.rs'),('bls12_381','src/scalar.rs')]:
 package=next(x for x in lock['package']if x['name']==name)
 root=f"{name}-{package['version']}"
 native=cache/'src/index.crates.io-1949cf8c6b5b557f'/root/relative
 copied=P/'qualified/context/runtime-library'/f'{root}-{Path(relative).name}'
 assert copied.read_bytes()==native.read_bytes()
 archive=cache/'cache/index.crates.io-1949cf8c6b5b557f'/f'{root}.crate'
 assert archive.stat().st_size<4*1024*1024 and sha(archive.read_bytes())==package['checksum']
 with tarfile.open(archive,'r:gz')as t:
  member=t.getmember(root+'/'+relative);assert member.isfile()and member.size<128*1024
  assert t.extractfile(member).read()==copied.read_bytes()
 library.append(dict(source=pin(copied),registry_archive=pin(archive),cargo_checksum=package['checksum'],exact_selected_member=True))
jubjub=(P/'qualified/context/runtime-library/jubjub-0.10.0-lib.rs').read_text()
scalar=(P/'qualified/context/runtime-library/bls12_381-0.8.0-scalar.rs').read_text()
assert 'pub use bls12_381::Scalar as Fq;'in jubjub
limbs=re.search(r'const MODULUS: Scalar = Scalar\(\[([\s\S]*?)\]\);',scalar).group(1)
words=[int(x.replace('_',''),16)for x in re.findall(r'0x([\da-f_]+)',limbs)]
assert len(words)==4
modulus=sum(n<<(64*i)for i,n in enumerate(words))
assert modulus==int(domain['modulus'])
source=(P/'source/ShielddSecurity/TransferBoundedNativeCodec01.lean').read_text()
assert f'def nullifierModulus : Nat := {modulus}'in source
assert 'Fq::from_bytes' in (P/'runtime/crates/crypto/primitives/src/encoding.rs').read_text()
assert 'pub struct Nullifier(pub Fq)' in (P/'runtime/crates/core/component/sct/src/nullifier.rs').read_text()
# Retained byte-only predecessor is a strict passed model, intentionally superseded.
Q=P/'superseded/byte-only01';plan=read(Q/'plan.json');result=[json.loads(l)for l in(Q/'events.jsonl').read_text().splitlines()][-1]['result'];target=plan['targets'][0]
old=(Q/'handwritten/TransferBoundedNativeCodec01.lean').read_bytes()
assert old==(Q/'project/ShielddSecurity/TransferBoundedNativeCodec01.lean').read_bytes()
assert len(old)==target['source']['bytes']and sha(old)==target['source']['sha256']
assert result['status']=='passed'and len(result['audits'])==13
log=Q/'runs/01-TransferBoundedNativeCodec01/stdout.txt'
assert pin(log)['sha256']==result['stdout']['sha256']and log.stat().st_size==result['stdout']['bytes']
parser=J/'windows-readback-publication-review01/verify_endpoint.py'
fn=next(x for x in ast.parse(parser.read_text()).body if isinstance(x,ast.FunctionDef)and x.name=='parse')
exec(compile(ast.Module(body=[fn],type_ignores=[]),str(parser),'exec'))
parse(log,target['audit_names'],result['audits'])
assert b'2 ^ 256'in old and old!=source.encode()
report=dict(status='PASSED',kind='Independent canonical native-domain and scoped proof-body review; no new Lean/native execution',runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',source=pin(P/'source/ShielddSecurity/TransferBoundedNativeCodec01.lean'),libraries=library,modulus=str(modulus),canonical_domain='Native Nullifier wraps Jubjub Fq alias to BLS12-381 Scalar; exact checksum-authenticated local crate source limbs agree with mathematical field modulus. Native from_bytes rejects noncanonical values. This is source correspondence, not a new verified implementation proof of field or library behavior.',contracts=['Supported NativePending has both opened ordered/member lists or sealed ordered list within32768 and each canonical key<shared field modulus. Coherent erase rebuilds member vector from the ordered vector.','Restricted restore/decode/encode roundtrip remains an explicit native primitive interface. Sum O NativePending totalization is proof-only for unsupported abstract keys; it is not a Rust enum declaration.','Successful bounded whole step derives next invariant/key domain and its actual stored pending object is in the native branch. Walk induction supplies the same result at each successful model step and final state from encoded default. Failure-partial native writes and internal SCT/flush/finalization operations are not closed by this endpoint.','Composed ordinary publication derives exact global request inputs and final observed root/Ready/boundary/current health under existing finalization field and successful execution interfaces. The theorem only exposes native-branch pending storage at the delivery final state; subsequent SCT seal/takeState encodings remain a successor obligation.','Other objects, typed getters/embedding/Clone/finite Rust collections, native action input projection/trace correspondence, component panic/finalization, snapshots/ICS23, temporal partition/poison/owner/locks/hash/serde/OS durability, native controls and full Transfer remain open.'],superseded=dict(source=pin(Q/'handwritten/TransferBoundedNativeCodec01.lean'),original_passed_reports=13,selected_fresh_reports=0,scope='Byte-only key<2^256 domain intentionally superseded with canonical field domain; fresh14 qualification reviewed separately; no alteration of accepted ancestor contracts'),fresh_complete_reports=14,full_transfer='OPEN',native_execution='UNRUN')
(J/'bounded-native-codec-rust-source-review02.json').write_text(json.dumps(report,indent=2)+'\n')
D=P.parent;a=read(D/'independent-review01.json');a['semantic_scope']=report['contracts'];a['native_domain_review']=pin(J/'bounded-native-codec-rust-source-review02.json');a['superseded_predecessor']=report['superseded'];(D/'semantic-source-review01.json').write_text(json.dumps(dict(status='PASSED',contracts=report['contracts'],native_domain=report['canonical_domain'],full_transfer='OPEN'),indent=2)+'\n');(D/'endpoint-audit-review01.json').write_text(json.dumps(a,indent=2)+'\n')
print(json.dumps(dict(status='PASSED',fresh_reports=14,checksum_authenticated_library_sources=2,superseded_preserved_reports=13,full_transfer='OPEN')))
