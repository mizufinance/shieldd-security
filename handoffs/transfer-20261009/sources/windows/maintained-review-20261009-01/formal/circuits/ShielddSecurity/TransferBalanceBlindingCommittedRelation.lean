import ShielddSecurity.TransferBalanceBlindingCanonicalFixedRelation

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferBalanceBlindingCommittedRelation

/-- The captured compiler assertion links committed column 2 to shadow 9.
Projection from the full carrier and native codec correspondence are separate. -/
def inputRows : List Row := [⟨[(2, (1 : Int)), (9, (-1 : Int))], []⟩]

def rows : List Row := inputRows ++ TransferBalanceBlindingCanonicalFixedRelation.rows

theorem input_binding {F : Type} [Field F] [CharP F Scalar.modulus]
    (rho : Nat → F) (satisfied : Satisfies rho inputRows) : rho 9 = rho 2 := by
  have checked : Compiler.checkRow Scalar.modulus inputRows
      ⟨Compiler.subtract [(2,1)] [(9,1)], []⟩ = true := by decide
  have equal := Compiler.checked_assertion_sound rho inputRows [(2,1)] [(9,1)]
    satisfied checked
  simp only [eval, Int.cast_one, one_mul, add_zero] at equal
  exact equal.symm

theorem sound {F : Type} [Field F] [CharP F Scalar.modulus]
    {J : Type} [AddCommGroup J]
    (model : Group.StandardCurveModel J
      ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (rho : Nat → F) (generator : J) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (imaginary : F)
    (nonSquare : Group.NoUnitSquare
      ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (baseMeaning : (RuntimeBalanceBlindingWindow000.base : Group.Point F) =
      model.coordinates generator)
    (satisfied : Satisfies rho rows) :
    let n := binary (RuntimeBalanceBlindingCanonical.decodedBits rho)
    n < Scalar.order ∧ (n : F) = rho 2 ∧
      GroupFixedCircuitCompletion.point rho
        TransferBalanceBlindingCanonicalFixedRelation.endpoint =
      model.coordinates (n • generator) := by
  have split : Satisfies rho inputRows ∧
      Satisfies rho TransferBalanceBlindingCanonicalFixedRelation.rows := by
    constructor
    · intro row member
      exact satisfied row (List.mem_append_left _ member)
    · intro row member
      exact satisfied row (List.mem_append_right _ member)
  have derived := TransferBalanceBlindingCanonicalFixedRelation.sound model rho generator
    one four imaginary nonSquare imaginarySquare baseMeaning split.2
  have privateMeaning : eval rho RuntimeBalanceBlindingCanonical.privateValue = rho 9 := by
    simp only [RuntimeBalanceBlindingCanonical.privateValue, eval, Int.cast_one,
      one_mul, add_zero]
  exact ⟨derived.1, derived.2.1.trans (privateMeaning.trans (input_binding rho split.1)),
    derived.2.2⟩

set_option pp.all true in
#check @input_binding
#print axioms input_binding
set_option pp.all true in
#check @sound
#print axioms sound

end ShielddSecurity.TransferBalanceBlindingCommittedRelation
