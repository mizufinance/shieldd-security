import ShielddSecurity.RuntimeBalanceBlindingTemplateCanonicalSoundness
import ShielddSecurity.RuntimeBalanceBlindingTemplateCanonicalPreservation
import ShielddSecurity.TransferBalanceBlindingFixedRowIdentity

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferBalanceBlindingCanonicalFixedRelation

def rows : List Row := RuntimeBalanceBlindingCanonical.originalRows ++
  RuntimeBalanceBlindingTemplateScalarSoundness.rows 0

def endpoint : Linear × Linear :=
  GroupFixedTemplateTrace.endpoint RuntimeBalanceBlindingTemplateOrdinaryTrace.input
    (RuntimeBalanceBlindingTemplateOrdinaryTrace.windows 0)

variable {F : Type} [Field F]
  [CharP F 52435875175126190479447740508185965837690552500527637822603658699938581184513]
  {J : Type} [AddCommGroup J]

/-- Arbitrary assignments to this fixed physical relation determine their own
canonical scalar and the corresponding group endpoint. -/
theorem sound
    (model : Group.StandardCurveModel J ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (rho : Nat → F) (generator : J) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (imaginary : F)
    (nonSquare : Group.NoUnitSquare ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (baseMeaning : (RuntimeBalanceBlindingWindow000.base : Group.Point F) = model.coordinates generator)
    (satisfied : Satisfies rho rows) :
    let n := binary (RuntimeBalanceBlindingCanonical.decodedBits rho)
    n < Scalar.order ∧ (n : F) = eval rho RuntimeBalanceBlindingCanonical.privateValue ∧
      GroupFixedCircuitCompletion.point rho endpoint = model.coordinates (n • generator) := by
  have adapted : Satisfies rho (RuntimeBalanceBlindingCanonical.originalRows ++
      RuntimeBalanceBlindingTemplateScalarSoundness.rows
        (binary (RuntimeBalanceBlindingCanonical.decodedBits rho))) := by
    rw [TransferBalanceBlindingFixedRowIdentity.rows_independent]
    exact satisfied
  have derived := RuntimeBalanceBlindingTemplateCanonicalSoundness.actual_canonical_and_fixed126_sound
    model rho generator one four imaginary nonSquare imaginarySquare baseMeaning adapted
  refine ⟨derived.1, derived.2.1, ?_⟩
  simpa only [TransferBalanceBlindingFixedRowIdentity.endpoint_independent] using derived.2.2

/-- A canonical scalar constructs the same fixed relation used by soundness. -/
theorem complete
    (model : Group.StandardCurveModel J ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (rho : Nat → F) (n : Nat) (generator : J) (canonical : n < Scalar.order)
    (meaning : rho 9 = (n : F)) (one : rho 0 = 1) (linked : rho 200692 = rho 0)
    (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (baseMeaning : (RuntimeBalanceBlindingWindow000.base : Group.Point F) = model.coordinates generator) :
    let completed := RuntimeBalanceBlindingTemplateCanonicalPreservation.construct rho n
    Satisfies completed rows ∧
      GroupFixedCircuitCompletion.point completed endpoint = model.coordinates (n • generator) := by
  have constructed := RuntimeBalanceBlindingTemplateCanonicalPreservation.actual_canonical_and_fixed126_complete
    model rho n generator canonical meaning one linked four imaginary nonSquare imaginarySquare baseMeaning
  constructor
  · change Satisfies _ (RuntimeBalanceBlindingCanonical.originalRows ++
      RuntimeBalanceBlindingTemplateScalarSoundness.rows 0)
    rw [← TransferBalanceBlindingFixedRowIdentity.rows_independent n]
    exact constructed.1
  · change GroupFixedCircuitCompletion.point _
      (GroupFixedTemplateTrace.endpoint RuntimeBalanceBlindingTemplateOrdinaryTrace.input
        (RuntimeBalanceBlindingTemplateOrdinaryTrace.windows 0)) = _
    rw [← TransferBalanceBlindingFixedRowIdentity.endpoint_independent n]
    exact constructed.2

set_option pp.all true in
#check @sound
#print axioms sound
set_option pp.all true in
#check @complete
#print axioms complete

end ShielddSecurity.TransferBalanceBlindingCanonicalFixedRelation
