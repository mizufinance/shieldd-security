import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.Ring

set_option maxHeartbeats 120000

namespace ShielddSecurity.OrbisPreAlgebra

variable {F : Type*} [Field F]

/-- A degree-one share polynomial conditioned on the share at index one being c.
This definition contains no statement about how either scalar is sampled. -/
def degreeOne (s c i : F) : F := (1 - i) * s + i * c

theorem share_at_zero (s c : F) : degreeOne s c 0 = s := by
  simp [degreeOne]

theorem share_at_corrupt_index (s c : F) : degreeOne s c 1 = c := by
  simp [degreeOne]

theorem fixed_two_three_weights (s c : F) :
    3 * degreeOne s c 2 - 2 * degreeOne s c 3 = s := by
  unfold degreeOne
  ring

section Points

variable {M : Type*} [AddCommGroup M] [Module F M]

def publicShare (S C : M) (i : F) : M := (1 - i) • S + i • C

/-- Algebraic public-share correspondence; group encoding and DKG refinement
are separate obligations. It applies independently to either module. -/
theorem public_share_correspondence (G : M) (s c i : F) :
    publicShare (s • G) (c • G) i = degreeOne s c i • G := by
  simp only [publicShare, degreeOne, smul_smul, add_smul]

/-- The scalar h is a supplied witness for a programmed hash point h • G.
This equality is not a hash-to-curve programming or signature-security proof. -/
theorem signing_oracle_simulation (G : M) (s c i h d_sig : F) :
    (h * d_sig) • publicShare (s • G) (c • G) i =
      (h * d_sig * degreeOne s c i) • G := by
  rw [public_share_correspondence, smul_smul]

/-- This equation requires the reader and ciphertext scalars x and u as inputs;
it neither extracts them from a PoP nor proves PoP knowledge soundness. -/
theorem valid_known_witness_share (G : M) (s c i d u x : F) :
    (d * degreeOne s c i) • (x • G + u • G) =
      (d * (u + x)) • (degreeOne s c i • G) := by
  rw [← add_smul, smul_smul, smul_smul]
  apply congrArg (fun a : F => a • G)
  ring

/-- Fixed honest indices two and three interpolate the constant term using
weights three and minus two. Arbitrary runtime participant selection is open. -/
theorem fixed_two_three_recovery (s c d : F) (R U : M) :
    (3 : F) • ((d * degreeOne s c 2) • (R + U)) -
      (2 : F) • ((d * degreeOne s c 3) • (R + U)) =
        (d * s) • (R + U) := by
  rw [smul_smul, smul_smul, ← sub_smul]
  apply congrArg (fun a : F => a • (R + U))
  calc
    _ = d * (3 * degreeOne s c 2 - 2 * degreeOne s c 3) := by ring
    _ = d * s := by rw [fixed_two_three_weights]

/-- Knowing x permits removal of the reader term from the recovered point.
The ciphertext point U is arbitrary; no discrete-log witness for U is required. -/
theorem known_reader_unblind (G U : M) (s d x : F) :
    (d * s) • (x • G + U) - (d * x) • (s • G) = (d * s) • U := by
  rw [smul_add, smul_smul, smul_smul]
  have coefficients : (d * s) * x = (d * x) * s := by ring
  rw [coefficients]
  exact add_sub_cancel_left _ _

end Points

section TwoGroups

variable {G1 G2 : Type*} [AddCommGroup G1] [Module F G1]
  [AddCommGroup G2] [Module F G2]

/-- The same scalar relation can be instantiated in two modules. This statement
does not claim that the runtime publishes G2 polynomial commitments. -/
theorem public_g1_g2_correspondence (g1 : G1) (g2 : G2) (s c i : F) :
    publicShare (s • g1) (c • g1) i = degreeOne s c i • g1 ∧
      publicShare (s • g2) (c • g2) i = degreeOne s c i • g2 := by
  exact ⟨public_share_correspondence g1 s c i,
    public_share_correspondence g2 s c i⟩

end TwoGroups

#check share_at_zero
#check share_at_corrupt_index
#check fixed_two_three_weights
#check public_share_correspondence
#check signing_oracle_simulation
#check valid_known_witness_share
#check fixed_two_three_recovery
#check known_reader_unblind
#check public_g1_g2_correspondence
#print axioms share_at_zero
#print axioms share_at_corrupt_index
#print axioms fixed_two_three_weights
#print axioms public_share_correspondence
#print axioms signing_oracle_simulation
#print axioms valid_known_witness_share
#print axioms fixed_two_three_recovery
#print axioms known_reader_unblind
#print axioms public_g1_g2_correspondence

end ShielddSecurity.OrbisPreAlgebra
