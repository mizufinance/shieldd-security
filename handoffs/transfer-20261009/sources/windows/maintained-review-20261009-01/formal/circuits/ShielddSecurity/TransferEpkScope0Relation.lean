import ShielddSecurity.TransferEpkCanonicalFixedRelation
import ShielddSecurity.RuntimeTransferEpk0CapturedPublication

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferEpkScope0Relation

def rows : List Row := TransferEpkCanonicalFixedRelation.rows ++
  RuntimeTransferEpk0CapturedPublication.rows

noncomputable def scalar {F : Type} [Field F] (rho : Nat → F) : Nat :=
  binary (RuntimeTransferEpk0Canonical.decodedBits rho)

variable {F : Type} [Field F]
  [CharP F 52435875175126190479447740508185965837690552500527637822603658699938581184513]

theorem sound {J : Type} [AddCommGroup J]
    (model : Group.StandardCurveModel J ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (rho : Nat → F) (generator : J) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (imaginary : F)
    (nonSquare : Group.NoUnitSquare ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (baseMeaning : (RuntimeTransferEpk0FixedWindow000.base : Group.Point F) = model.coordinates generator)
    (satisfied : Satisfies rho rows) :
    0 < scalar rho ∧ scalar rho < Scalar.order ∧ (scalar rho : F) = rho 4930 ∧
      (⟨rho 4922,rho 4923⟩ : Group.Point F) = model.coordinates (scalar rho • generator) := by
  have groupRows : Satisfies rho TransferEpkCanonicalFixedRelation.rows := by
    intro row member
    exact satisfied row (List.mem_append_left _ member)
  have publicationRows : Satisfies rho RuntimeTransferEpk0CapturedPublication.rows := by
    intro row member
    exact satisfied row (List.mem_append_right _ member)
  have derived := TransferEpkCanonicalFixedRelation.sound model rho generator one four
    imaginary nonSquare imaginarySquare baseMeaning groupRows
  change scalar rho < Scalar.order ∧
    (scalar rho : F) = eval rho RuntimeTransferEpk0Canonical.privateValue ∧
    GroupFixedCircuitCompletion.point rho TransferEpkCanonicalFixedRelation.endpoint =
      model.coordinates (scalar rho • generator) at derived
  have amount : (scalar rho : F) = rho 4930 := by
    simpa only [RuntimeTransferEpk0Canonical.privateValue,eval,Int.cast_one,one_mul,add_zero] using derived.2.1
  have endpoint := derived.2.2
  change (⟨eval rho [(5433,1)],eval rho [(5434,1)]⟩ : Group.Point F) = _ at endpoint
  simp only [eval,Int.cast_one,one_mul,add_zero] at endpoint
  have publication := RuntimeTransferEpk0CapturedPublication.publication_sound rho publicationRows
  have published : (⟨rho 4922,rho 4923⟩ : Group.Point F) =
      model.coordinates (scalar rho • generator) := by
    rw [← publication.1,← publication.2.1]
    exact endpoint
  have nonzero := (RuntimeTransferEpk0CapturedPublication.inverse_sound rho four one publicationRows).2
  have positive : 0 < scalar rho := by
    by_contra absent
    have zero : scalar rho = 0 := Nat.eq_zero_of_not_pos absent
    have x := congrArg Group.Point.x published
    simp only [zero,zero_nsmul,model.identity,Group.identityPoint] at x
    exact nonzero x
  exact ⟨positive,derived.1,amount,published⟩

set_option pp.all true in
#check @sound
#print axioms sound

end ShielddSecurity.TransferEpkScope0Relation
