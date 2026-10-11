"""Narrow supported domain to canonical Jubjub Fq, preserving byte-only run."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-bounded-native-codec-20261011-01'
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
lib=ROOT/'context/runtime-library'
jubjub=(lib/'jubjub-0.10.0-lib.rs').read_text()
scalar=(lib/'bls12_381-0.8.0-scalar.rs').read_text()
assert hashlib.sha256((lib/'jubjub-0.10.0-lib.rs').read_bytes()).hexdigest()=='2cda8d5fa806db35bfced2aa6fbea4389447714c45aa8a25eef069a775ea5598'
assert hashlib.sha256((lib/'bls12_381-0.8.0-scalar.rs').read_bytes()).hexdigest()=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475'
assert 'pub use bls12_381::Scalar as Fq;' in jubjub
match=re.search(r'const MODULUS: Scalar = Scalar\(\[([^]]+)\]\);',scalar)
assert match
limbs=re.findall(r'0x([0-9a-fA-F_]+)',match.group(1));assert len(limbs)==4
modulus=sum(int(limb.replace('_',''),16)<<(64*i) for i,limb in enumerate(limbs))
assert modulus==int('73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001',16)
assert modulus==52435875175126190479447740508185965837690552500527637822603658699938581184513
math_source=DIAG.parent.parent/'circuits/ShielddSecurity/Scalar.lean'
assert f'def modulus : Nat := {modulus}' in math_source.read_text()
runtime=Path('C:/src/shieldd-pr160-844389ee')
nullifier=runtime/'crates/core/component/sct/src/nullifier.rs'
encoding=runtime/'crates/crypto/primitives/src/encoding.rs'
primitives=runtime/'crates/crypto/primitives/src/lib.rs'
assert 'pub struct Nullifier(pub Fq);' in nullifier.read_text()
assert 'Option::from(Fq::from_bytes(bytes))' in encoding.read_text()
assert 'pub use jubjub::{Fq, Fr, SubgroupPoint};' in primitives.read_text()
def pin(p):
    data=Path(p).read_bytes();return dict(path=str(p),bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
domain=dict(kind='SOURCE_CANONICAL_NULLIFIER_FIELD_DOMAIN_EXTRACTION',modulus=str(modulus),limbs=limbs,
    library_sources=[pin(lib/n) for n in ['jubjub-0.10.0-lib.rs','bls12_381-0.8.0-scalar.rs','source-copy.json']],
    runtime_sources=[pin(p) for p in [nullifier,encoding,primitives,runtime/'Cargo.lock']],math_source=pin(math_source),
    scope='Exact Nullifier Fq alias, canonical from_bytes path and pinned registry modulus/source identity. Shared field mathematical certificate reused; no new field proof or native FFI/Clone/Vec/OrdSet/primitive semantic proof or executed control.')
domain_bytes=(json.dumps(domain,sort_keys=True,indent=2)+'\n').encode()
domain_file=ROOT/'context/canonical-domain.json'
if domain_file.exists():
    assert json.loads(domain_file.read_bytes())==domain
else:
    domain_file.write_bytes(domain_bytes)
source=(old/'handwritten/TransferBoundedNativeCodec01.lean').read_text()
assert source.count('2 ^ 256')==12,source.count('2 ^ 256')
source=source.replace('2 ^ 256','nullifierModulus')
anchor='def BoundedPending';assert source.count(anchor)==1
source=source.replace(anchor,f'def nullifierModulus : Nat := {modulus}\n\n'+anchor)
source=source.replace('256-bit nullifier identities','canonical Jubjub Fq nullifier identities')
anchor='set_option pp.all true in\n#check @BoundedPending';assert source.count(anchor)==1
source=source.replace(anchor,'set_option pp.all true in\n#check @nullifierModulus\n#print axioms nullifierModulus\n'+anchor)
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferBoundedNativeCodec01.lean').write_text(source)
s=(old/'prepare.py').read_text()
a="POOL = DIAG / 'transfer-bounded-native-codec-owned-floor-20261011-01'";assert s.count(a)==1
s=s.replace(a,"POOL = DIAG / 'transfer-bounded-native-codec-owned-floor-20261011-02'")
s=s.replace('assert len(names) == 13','assert len(names) == 14').replace("'fresh_audits': 13, 'inherited_audits': 701","'fresh_audits': 14, 'inherited_audits': 701")
s=s.replace('every projected nullifier key below2^256','every projected nullifier key is a canonical Jubjub Fq value below the exact shared-field modulus52435875175126190479447740508185965837690552500527637822603658699938581184513')
s=s.replace('Thirteen complete reports (five definitions, eight proofs)','Fourteen complete reports (six definitions including exact source-extracted canonical field modulus, eight proofs)')
anchor="mapping_file = ROOT / 'source-mapping.json'";assert s.count(anchor)==1
extra="domain = json.loads((ROOT/'context/canonical-domain.json').read_bytes())\nfor row in domain['runtime_sources']:\n    assert row['path'] not in runtime_rows or runtime_rows[row['path']] == row\n    runtime_rows[row['path']] = row\nmapping['runtime_sources'] = list(runtime_rows.values())\nmapping['canonical_nullifier_domain'] = domain\nmapping['library_sources'] = domain['library_sources']\n"
s=s.replace(anchor,extra+anchor)
anchor="plan['pins'] += mapping['runtime_sources']";assert s.count(anchor)==1
s=s.replace(anchor,"plan['pins'].append(pin(ROOT/'prepare_recipe_count_failure.py'))\n"+anchor)
anchor="plan['pins'] += mapping['runtime_sources']";assert s.count(anchor)==1
extra="superseded_byte_only = DIAG/'transfer-bounded-native-codec-20261011-01'\nplan['pins'] += [pin(superseded_byte_only/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferBoundedNativeCodec01.lean','project/ShielddSecurity/TransferBoundedNativeCodec01.lean','runs/01-TransferBoundedNativeCodec01/stdout.txt']]\nplan['pins'] += [pin(ROOT/'context/canonical-domain.json')] + domain['library_sources'] + [domain['math_source']]\n"
s=s.replace(anchor,extra+anchor)
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Byte-only source01 strict passed13 but unpublished/superseded, not selected or replayed; byte bound admits noncanonical Fq identities. Source02 restricts all modeled native key domains to exact canonical Fq modulus extracted from pinned source chain and shared with existing actual-field certificate. Definitions/premises/conclusions intentionally narrowed; same symbolic proofs. No native/control credit or guard changes.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'canonical_nullifier_modulus':str(modulus),'fresh_declarations':14,'superseded_byte_only_native_credit':0})
