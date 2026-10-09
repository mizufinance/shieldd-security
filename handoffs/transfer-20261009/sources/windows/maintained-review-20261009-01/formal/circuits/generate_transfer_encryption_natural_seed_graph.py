"""Recover the four actual tier seeds as canonical modular subtraction."""
import re

NAME = 'TransferEncryptionNaturalSeedGraph'
FIELD = 'RuntimeTransferEncryptionFieldCipherGraph'
SEEDS = [(0, 12, 10, 8517), (1, 17, 16, 8522),
         (2, 15, 13, 8528), (3, 21, 20, 8533)]


def generate(seeds):
    assert seeds == SEEDS
    source = f'''import ShielddSecurity.{FIELD}
import ShielddSecurity.CanonicalFieldSubtraction
set_option maxHeartbeats 400000
namespace ShielddSecurity.{NAME}
variable {{F : Type}} [Field F] [CharP F Scalar.modulus]
variable (codec : TransferReduction.CanonicalField F)
/-- The same operation as TransferSem.fsub, using the actual field modulus. -/
def subtractNat (left right : Nat) : Nat :=
  (left % Scalar.modulus + Scalar.modulus - right % Scalar.modulus) % Scalar.modulus
'''
    exports = []
    for tier, _, secret, _ in seeds:
        source += f'''/-- The seed is recovered from the actual c2 and shared-secret hash;
neither the seed nor a desired cipher result is supplied as a premise. -/
theorem seed{tier}_natural (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho {FIELD}.rawRows) :
    codec.decode ({FIELD}.seed{tier} rho) =
      subtractNat (codec.decode (eval rho {FIELD}.c2_{tier}))
        (codec.decode ({FIELD}.hashValue rho {secret})) := by
  have recovered : {FIELD}.seed{tier} rho =
      eval rho {FIELD}.c2_{tier} - {FIELD}.hashValue rho {secret} := by
    rw [{FIELD}.c2_seed{tier}_sound rho one satisfied, add_sub_cancel_right]
  rw [recovered, CanonicalFieldSubtraction.decode_sub]
  rfl
'''
        exports.append(f'ShielddSecurity.{NAME}.seed{tier}_natural')
    source += f'end ShielddSecurity.{NAME}\n'
    source += ''.join(f'set_option pp.all true in\n#check @{name}\n#print axioms {name}\n'
                      for name in exports)
    assert len(exports) == 4
    assert re.findall(r'^#check @([\w.]+)$', source, re.M) == exports
    assert re.findall(r'^#print axioms ([\w.]+)$', source, re.M) == exports
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', source)
    return source, exports
