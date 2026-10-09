import ShielddSecurity.GroupSubgroupSourceGraph
import ShielddSecurity.TransferFirstSubgroupFinal01

set_option maxHeartbeats 500000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferFirstSubgroupSemantics01
open Compiler GroupSubgroupGraphArithmetic GroupSubgroupSourceGraph
variable {F : Type} [Field F]

/-! The concrete first registry-dk source cone consumes the published generated
graph. Shape matching checks typed source operations and all six assertion
pairs. This is a graph semantic instance, not the complete Transfer relation,
original-row witness completion, or a deployed curve/codec/Crypto instance. -/

def d : Int := 19257038036680949359750312669786877991949435402254120286184196891950884077233
def negative : Int := 52435875175126190479447740508185965837690552500527637822603658699938581184512

theorem graph_matches : Matches TransferFirstSubgroupData01.graph d negative := by
  constructor
  · intro index
    fin_cases index <;> rfl
  · rfl

theorem negative_cast [CharP F Scalar.modulus] : (negative : F) = -1 := by
  rw [show negative = (Scalar.modulus : Int) - 1 by norm_num [negative, Scalar.modulus]]
  exact modulus_negative_one

theorem small_cast_ne_zero [CharP F Scalar.modulus] (value : Nat)
    (positive : 0 < value) (before : value < Scalar.modulus) : (value : F) ≠ 0 := by
  intro zero
  have divides : Scalar.modulus ∣ value := (CharP.cast_eq_zero_iff F Scalar.modulus value).mp zero
  exact Nat.not_le_of_gt before (Nat.le_of_dvd positive divides)

theorem two_ne_zero [CharP F Scalar.modulus] : (2 : F) ≠ 0 := by
  simpa only [Nat.cast_ofNat] using small_cast_ne_zero (F := F) 2 (by decide) (by decide)

theorem four_ne_zero [CharP F Scalar.modulus] : (4 : F) ≠ 0 := by
  simpa only [Nat.cast_ofNat] using small_cast_ne_zero (F := F) 4 (by decide) (by decide)

theorem satisfying_graph_sound [CharP F Scalar.modulus]
    (inputs : Nat → F) (computed : Fin 80 → F)
    (satisfied : GraphSatisfies TransferFirstSubgroupData01.graph inputs computed) :
    Group.OnCurve (d : F) (preimage inputs) ∧
      GroupNativeCofactor.nativeEight (d : F) (preimage inputs) = point inputs :=
  graph_satisfies_sound TransferFirstSubgroupData01.graph d negative inputs computed
    negative_cast graph_matches satisfied

theorem assertions_complete [CharP F Scalar.modulus]
    (initial : Group.Point F) (remaining : Nat → F)
    (valid : Group.OnCurve (d : F) initial)
    (denominators : ∀ index < 3, inverseProduct (d : F) (nativeTrace (d : F) initial index) ≠ 0) :
    let inputs := constructedInputs (d : F) initial remaining
    ∀ assertion ∈ TransferFirstSubgroupData01.graph.assertions,
      SourceGraphEvaluation.values TransferFirstSubgroupData01.graph inputs assertion.1 =
        SourceGraphEvaluation.values TransferFirstSubgroupData01.graph inputs assertion.2 :=
  graph_assertions_complete TransferFirstSubgroupData01.graph d negative initial remaining
    negative_cast graph_matches valid denominators

theorem native_assertions_complete [CharP F Scalar.modulus]
    {J : Type} [AddCommGroup J] (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (imaginary : F)
    (model : Group.StandardCurveModel J (d : F)) (nonSquare : Group.NoUnitSquare (d : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (initial : J) (subgroup : Scalar.order • initial = 0) (remaining : Nat → F) :
    let q := GroupNativeCofactor.nativePreimage (d : F) codec writer (model.coordinates initial)
    let inputs := constructedInputs (d : F) q remaining
    point inputs = model.coordinates initial ∧ preimage inputs = q ∧
      ∀ assertion ∈ TransferFirstSubgroupData01.graph.assertions,
        SourceGraphEvaluation.values TransferFirstSubgroupData01.graph inputs assertion.1 =
          SourceGraphEvaluation.values TransferFirstSubgroupData01.graph inputs assertion.2 :=
  native_graph_assertions_complete TransferFirstSubgroupData01.graph d negative codec writer imaginary model
    negative_cast graph_matches nonSquare imaginarySquare two_ne_zero initial subgroup remaining

theorem original_rows_sound [CharP F Scalar.modulus]
    (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho TransferFirstSubgroupData01.originalRows.toList) :
    Group.OnCurve (d : F) (⟨rho 16, rho 17⟩ : Group.Point F) ∧
      GroupNativeCofactor.nativeEight (d : F) (⟨rho 16, rho 17⟩ : Group.Point F) =
        (⟨rho 14, rho 15⟩ : Group.Point F) := by
  have assertions := (TransferFirstSubgroupCertificates01.arbitrary_assignment_sound rho one four_ne_zero satisfied).2
  have meaning := graph_assertions_sound TransferFirstSubgroupData01.graph d negative
    (fun input => eval rho (TransferFirstSubgroupData01.inputTerms input)) negative_cast graph_matches assertions
  simpa [preimage, point, TransferFirstSubgroupData01.inputTerms, eval] using meaning

/-- Construct the actual selected original rows from an independently admitted
subgroup point. The six source assertions are conclusions of the native curve
argument. The other source inputs are preserved, with no legality claim for
the remaining full Transfer graph. Identity keys are permitted. -/
theorem native_original_rows_complete [CharP F Scalar.modulus]
    {J : Type} [AddCommGroup J] (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (imaginary : F)
    (model : Group.StandardCurveModel J (d : F)) (nonSquare : Group.NoUnitSquare (d : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (initial : J) (subgroup : Scalar.order • initial = 0) (remaining : Nat → F) :
    let q := GroupNativeCofactor.nativePreimage (d : F) codec writer (model.coordinates initial)
    let inputs := constructedInputs (d : F) q remaining
    let rho := TransferFirstSubgroupCompletion01.completed inputs
    Satisfies rho TransferFirstSubgroupData01.originalRows.toList ∧
      (∀ input < 22735, rho (3 + input) = inputs input) ∧
      rho 0 = 1 ∧ rho TransferFirstSubgroupData01.copy = 1 ∧
      point inputs = model.coordinates initial ∧ preimage inputs = q := by
  dsimp only
  have semantic := native_assertions_complete codec writer imaginary model nonSquare
    imaginarySquare initial subgroup remaining
  have rows := TransferFirstSubgroupFinal01.constructive_slice_complete
    (constructedInputs (d : F)
      (GroupNativeCofactor.nativePreimage (d : F) codec writer (model.coordinates initial)) remaining)
    four_ne_zero semantic.2.2
  exact ⟨rows.1, rows.2.1, rows.2.2.1, rows.2.2.2, semantic.1, semantic.2.1⟩

end ShielddSecurity.TransferFirstSubgroupSemantics01
