import ShielddSecurity.WeierstrassTwoTorsionAlgebra01

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.EulerNonsquare01

variable {F : Type} [Field F]

/-- The concrete residue check and Fermat exponent must be supplied by the
certified field instance. This lemma only joins those statements algebraically. -/
theorem nonsquare_from_euler (value : F) (half : Nat)
    (nonzero : value ≠ 0) (two : (2 : F) ≠ 0)
    (fermat : ∀ root : F, root ≠ 0 → root ^ (2 * half) = 1)
    (euler : value ^ half = -1) :
    WeierstrassTwoTorsionAlgebra01.NoSquare value := by
  intro root square
  have squarePow : root ^ 2 = value := by simpa only [pow_two] using square
  have rootNonzero : root ≠ 0 := by
    intro zero
    apply nonzero
    rw [← squarePow, zero, zero_pow (by decide : 2 ≠ 0)]
  have one : value ^ half = 1 := by
    rw [← squarePow, ← pow_mul]
    exact fermat root rootNonzero
  have sign : (1 : F) = -1 := one.symm.trans euler
  apply two
  calc
    (2 : F) = 1 + 1 := by ring
    _ = 1 + (-1) := congrArg (fun x : F => 1 + x) sign
    _ = 0 := add_neg_cancel 1

end ShielddSecurity.EulerNonsquare01

set_option pp.all true in
#check @ShielddSecurity.EulerNonsquare01.nonsquare_from_euler
#print axioms ShielddSecurity.EulerNonsquare01.nonsquare_from_euler
