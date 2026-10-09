import ShielddSecurity.RuntimeTransferEpk0FixedTemplateCanonicalSoundness
import ShielddSecurity.RuntimeTransferEpk0FixedTemplateCanonicalPreservation
import ShielddSecurity.TransferEpkFixedRowIdentity

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferEpkCanonicalFixedRelation

def rows : List Row := RuntimeTransferEpk0Canonical.originalRows ++
  RuntimeTransferEpk0FixedTemplateScalarSoundness.rows 0

def endpoint : Linear × Linear :=
  GroupFixedTemplateTrace.endpoint RuntimeTransferEpk0FixedTemplateOrdinaryTrace.input
    (RuntimeTransferEpk0FixedTemplateOrdinaryTrace.windows 0)

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
    (baseMeaning : (RuntimeTransferEpk0FixedWindow000.base : Group.Point F) = model.coordinates generator)
    (satisfied : Satisfies rho rows) :
    let n := binary (RuntimeTransferEpk0Canonical.decodedBits rho)
    n < Scalar.order ∧ (n : F) = eval rho RuntimeTransferEpk0Canonical.privateValue ∧
      GroupFixedCircuitCompletion.point rho endpoint = model.coordinates (n • generator) := by
  have adapted : Satisfies rho (RuntimeTransferEpk0Canonical.originalRows ++
      RuntimeTransferEpk0FixedTemplateScalarSoundness.rows
        (binary (RuntimeTransferEpk0Canonical.decodedBits rho))) := by
    rw [TransferEpkFixedRowIdentity.rows_independent]
    exact satisfied
  have derived := RuntimeTransferEpk0FixedTemplateCanonicalSoundness.actual_canonical_and_fixed126_sound
    model rho generator one four imaginary nonSquare imaginarySquare baseMeaning adapted
  refine ⟨derived.1, derived.2.1, ?_⟩
  simpa only [TransferEpkFixedRowIdentity.endpoint_independent] using derived.2.2

/-- A canonical scalar constructs the same fixed relation used by soundness. -/
theorem complete
    (model : Group.StandardCurveModel J ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (rho : Nat → F) (n : Nat) (generator : J) (canonical : n < Scalar.order)
    (meaning : rho 4930 = (n : F)) (one : rho 0 = 1) (linked : rho 200692 = rho 0)
    (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (baseMeaning : (RuntimeTransferEpk0FixedWindow000.base : Group.Point F) = model.coordinates generator) :
    let completed := RuntimeTransferEpk0FixedTemplateCanonicalPreservation.construct rho n
    Satisfies completed rows ∧
      GroupFixedCircuitCompletion.point completed endpoint = model.coordinates (n • generator) := by
  have constructed := RuntimeTransferEpk0FixedTemplateCanonicalPreservation.actual_canonical_and_fixed126_complete
    model rho n generator canonical meaning one linked four imaginary nonSquare imaginarySquare baseMeaning
  constructor
  · change Satisfies _ (RuntimeTransferEpk0Canonical.originalRows ++
      RuntimeTransferEpk0FixedTemplateScalarSoundness.rows 0)
    rw [← TransferEpkFixedRowIdentity.rows_independent n]
    exact constructed.1
  · change GroupFixedCircuitCompletion.point _
      (GroupFixedTemplateTrace.endpoint RuntimeTransferEpk0FixedTemplateOrdinaryTrace.input
        (RuntimeTransferEpk0FixedTemplateOrdinaryTrace.windows 0)) = _
    rw [← TransferEpkFixedRowIdentity.endpoint_independent n]
    exact constructed.2

set_option pp.all true in
#check @sound
#print axioms sound
set_option pp.all true in
#check @complete
#print axioms complete

end ShielddSecurity.TransferEpkCanonicalFixedRelation
