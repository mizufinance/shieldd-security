import ShielddSecurity.TransferBalanceBlindingCommittedRelation
import ShielddSecurity.RuntimeBalanceBlindingTemplateFrameBounds

set_option maxHeartbeats 250000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferBalanceBlindingCommittedCompletion

theorem input_rows_preserved {F : Type} [Field F] (rho : Nat → F) (n : Nat)
    (linkedInput : rho 9 = rho 2) :
    Satisfies (RuntimeBalanceBlindingTemplateCanonicalPreservation.construct rho n)
      TransferBalanceBlindingCommittedRelation.inputRows := by
  have first := RuntimeBalanceBlindingTemplateFrameBounds.preserves_covered
    rho n 2 (by decide)
  have second := RuntimeBalanceBlindingTemplateFrameBounds.preserves_covered
    rho n 9 (by decide)
  intro row member
  simp only [TransferBalanceBlindingCommittedRelation.inputRows,
    List.mem_singleton] at member
  subst row
  simp only [Square, eval, Int.cast_one, Int.cast_neg, one_mul, add_zero]
  rw [first, second, linkedInput]
  ring

/-- Construct the same committed/input/H physical relation used by soundness.
The full carrier projection and the native representation of n are separate. -/
theorem complete {F : Type} [Field F] [CharP F Scalar.modulus]
    {J : Type} [AddCommGroup J]
    (model : Group.StandardCurveModel J
      ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (rho : Nat → F) (n : Nat) (generator : J) (canonical : n < Scalar.order)
    (committed : rho 2 = (n : F)) (linkedInput : rho 9 = rho 2)
    (one : rho 0 = 1) (linkedCopy : rho 200692 = rho 0)
    (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare
      ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (baseMeaning : (RuntimeBalanceBlindingWindow000.base : Group.Point F) =
      model.coordinates generator) :
    let completed := RuntimeBalanceBlindingTemplateCanonicalPreservation.construct rho n
    Satisfies completed TransferBalanceBlindingCommittedRelation.rows ∧
      GroupFixedCircuitCompletion.point completed
        TransferBalanceBlindingCanonicalFixedRelation.endpoint =
      model.coordinates (n • generator) := by
  have fixed := TransferBalanceBlindingCanonicalFixedRelation.complete model rho n generator
    canonical (linkedInput.trans committed) one linkedCopy four imaginary
    nonSquare imaginarySquare baseMeaning
  have input := input_rows_preserved rho n linkedInput
  refine ⟨?_, fixed.2⟩
  intro row member
  rcases List.mem_append.mp member with earlier | later
  · exact input row earlier
  · exact fixed.1 row later

set_option pp.all true in
#check @input_rows_preserved
#print axioms input_rows_preserved
set_option pp.all true in
#check @complete
#print axioms complete

end ShielddSecurity.TransferBalanceBlindingCommittedCompletion
