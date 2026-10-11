"""Bounded independent integer/source comparison, never a kernel receipt."""
import hashlib
import json
import re
from pathlib import Path

CAMPAIGN = Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can')
G = CAMPAIGN / 'work/shared-build-handoff/handoffs/transfer-20261009'
OUT = Path(__file__).parent
CRATE = Path('/Users/antoinecyr/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/reddsa-0.5.2')
proposal_path = G / 'sources/parent/weierstrass-order-inputs01/proposal.json'
constants_path = CRATE / 'src/constants.rs'
algebra_path = G / 'sources/windows/edwards-rational-equivalence-20261009-01/circuits/ShielddSecurity/EdwardsWeierstrassAlgebra01.lean'
generator_path = CAMPAIGN / 'work/runtime-snapshot/crates/crypto/primitives/src/generators.rs'

p = 52435875175126190479447740508185965837690552500527637822603658699938581184513
d = -10240 * pow(10241, -1, p) % p
B = -40964 % p
X, Y = json.loads(proposal_path.read_text())['base']
assert Y % p and (X + B) % p
x = B * X * pow(Y, -1, p) % p
y = (X - B) * pow((X + B) % p, -1, p) % p
assert (y*y - x*x - 1 - d*x*x*y*y) % p == 0
assert B * (1+y) * pow((1-y) % p, -1, p) % p == X
assert B*B * (1+y) * pow(((1-y)*x) % p, -1, p) % p == Y
algebra = algebra_path.read_text()
assert 'def inverseX (B X Y : F) : F := B * X / Y' in algebra
assert 'def inverseY (B X : F) : F := (X - B) / (X + B)' in algebra
compressed = bytearray(y.to_bytes(32, 'little'))
compressed[31] |= (x & 1) << 7
match = re.search(r'pub const SPENDAUTHSIG_BASEPOINT_BYTES: \[u8; 32\] = \[(.*?)\];', constants_path.read_text(), re.S)
assert match
sdk = bytes(map(int, re.findall(r'\d+', match.group(1))))
assert len(sdk) == 32
assert bytes(compressed) != sdk
paths = [proposal_path, constants_path, algebra_path, generator_path,
         CRATE/'src/lib.rs', CRATE/'src/signing_key.rs', CRATE/'src/verification_key.rs']
report = {
    'kind': 'independent bounded integer and pinned-source identity comparison',
    'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'source_pins': [{'path': str(f), 'bytes': f.stat().st_size,
                     'sha256': hashlib.sha256(f.read_bytes()).hexdigest()} for f in paths],
    'traced_base_weierstrass': [str(X), str(Y)],
    'traced_base_edwards': [str(x), str(y)],
    'traced_base_compressed_hex': bytes(compressed).hex(),
    'reddsa_spend_auth_constant_hex': sdk.hex(),
    'equal': False,
    'checks': ['Edwards equation', 'both forward coordinate roundtrips',
               'inverse coordinate formulas match exact retained Lean source',
               '32-byte constant extracted from exact locked reddsa source'],
    'source_path': ['SDK canonical signing scalar one', 'reddsa SigningKey caches VerificationKey::from scalar',
                    'reddsa VerificationKey::from computes SpendAuth basepoint times scalar',
                    'SpendAuth basepoint decodes SPENDAUTHSIG_BASEPOINT_BYTES',
                    'SDK SubgroupPoint::from_bytes consumes the resulting verification-key bytes'],
    'scope': 'Data/source comparison only. SDK initialization, scalar-one identity, codec and subgroup claims still require owned correspondence proofs. The actual curve-order proof uses the distinct traced base and remains valid.',
    'kernel_replay': False,
    'full_transfer': 'OPEN',
}
target = OUT/'base-identity-comparison01.json'
target.write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps({'report':str(target),'equal':False,'traced_hex':bytes(compressed).hex(),'sdk_hex':sdk.hex()}))
