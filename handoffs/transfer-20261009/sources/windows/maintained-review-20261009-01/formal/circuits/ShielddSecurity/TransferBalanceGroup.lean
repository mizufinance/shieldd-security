import ShielddSecurity.TransferBalance
import ShielddSecurity.TransferConservation
import Mathlib.Algebra.Group.Basic

set_option maxHeartbeats 100000

namespace ShielddSecurity.TransferBalanceGroup

def groupSum {G : Type} [AddCommGroup G] : List G → G
  | [] => 0
  | value :: rest => value + groupSum rest

/-- Each ordered occurrence supplies its extracted value term and its blinding.
The list includes an optional fee-funding action exactly once. It may contain
duplicate values/assets; no set conversion is permitted. -/
def nativeBalanceSum {G : Type} [AddCommGroup G] (terms : List (G × Int))
    (blindingGenerator : G) : G :=
  groupSum (terms.map (fun term => term.1 + term.2 • blindingGenerator))

theorem action_commitment_sum {G : Type} [AddCommGroup G] (terms : List (G × Int))
    (blindingGenerator : G) :
    nativeBalanceSum terms blindingGenerator = groupSum (terms.map Prod.fst) +
      TransferConservation.signedSum (terms.map Prod.snd) • blindingGenerator := by
  unfold nativeBalanceSum
  induction terms with
  | nil => simp [groupSum, TransferConservation.signedSum]
  | cons term rest ih =>
      simp only [List.map_cons, groupSum, TransferConservation.signedSum]
      rw [ih, add_zsmul]
      exact add_add_add_comm _ _ _ _

/-- Fee::balance is negative, and native binding_verification_key adds its
zero-blinding commitment once after body plus optional fee-funding actions. -/
theorem transaction_commitment_decomposition {G : Type} [AddCommGroup G]
    (terms : List (G × Int)) (blindingGenerator feeGenerator : G) (fee : Nat) :
    nativeBalanceSum terms blindingGenerator - (fee : Int) • feeGenerator =
      (groupSum (terms.map Prod.fst) - (fee : Int) • feeGenerator) +
        TransferConservation.signedSum (terms.map Prod.snd) • blindingGenerator := by
  rw [action_commitment_sum]
  exact add_sub_right_comm _ _ _

/-- If the named binding-signature knowledge contract extracts an opening of
the native aggregate key in the blinding generator, nonzero semantic value
terms yield this alternative representation. This is the reduction boundary
for computational multi-asset binding, not universal generator independence or
a consequence of signature verification alone. Rust/codec joins remain open. -/
theorem extracted_binding_opening_representation {G : Type} [AddCommGroup G]
    (terms : List (G × Int)) (blindingGenerator feeGenerator : G)
    (fee : Nat) (signatureOpening : Int)
    (extracted : nativeBalanceSum terms blindingGenerator - (fee : Int) • feeGenerator =
      signatureOpening • blindingGenerator) :
    groupSum (terms.map Prod.fst) - (fee : Int) • feeGenerator =
      (signatureOpening - TransferConservation.signedSum (terms.map Prod.snd)) •
        blindingGenerator := by
  calc
    _ = (nativeBalanceSum terms blindingGenerator - (fee : Int) • feeGenerator) -
        TransferConservation.signedSum (terms.map Prod.snd) • blindingGenerator := by
      rw [transaction_commitment_decomposition]
      exact (add_sub_cancel_right _ _).symm
    _ = signatureOpening • blindingGenerator -
        TransferConservation.signedSum (terms.map Prod.snd) • blindingGenerator := by rw [extracted]
    _ = _ := by
      simpa only [sub_eq_add_neg] using (sub_zsmul blindingGenerator signatureOpening
        (TransferConservation.signedSum (terms.map Prod.snd))).symm

/-- One occurrence extracted from the corresponding Transfer proof contract.
This list covers body plus optional fee funding, never a set of distinct assets.
The integer/scalar/group/native correspondence is a separate owned refinement. -/
structure ActionOpening where
  asset : Nat
  value : Int
  blinding : Int

def semanticActions (openings : List ActionOpening) : List (Nat × Int) :=
  openings.map (fun opening => (opening.asset, opening.value))

def nativeTerms {G : Type} [AddCommGroup G] (generators : Nat → G)
    (openings : List ActionOpening) : List (G × Int) :=
  openings.map (fun opening => (opening.value • generators opening.asset, opening.blinding))

/-- Every conservation-violating extracted witness, together with a binding
signature secret opening, gives an explicit alternative value representation
with a nonzero scalar coefficient. The bound forbids a modular-wrap explanation.
Computational commitment binding must bound this event for the registered asset
generators; this theorem does not assert universal independence or conservation. -/
theorem nonconservation_exposes_representation_event
    {S : Type} [Field S] [CharP S ShielddSecurity.Scalar.order]
    {G : Type} [AddCommGroup G] (generators : Nat → G) (blindingGenerator : G)
    (openings : List ActionOpening) (asset feeAsset feeAmount : Nat)
    (signatureOpening : Int) (count : openings.length ≤ 512)
    (bounded : ∀ opening ∈ openings, opening.value.natAbs < 2^129)
    (feeBound : feeAmount < 2^128)
    (different : TransferConservation.signedSum
      (TransferConservation.selectedValues asset (semanticActions openings)) ≠
        (TransferConservation.selectedFee asset feeAsset feeAmount : Int))
    (extracted : nativeBalanceSum (nativeTerms generators openings) blindingGenerator -
      (feeAmount : Int) • generators feeAsset = signatureOpening • blindingGenerator) :
    ∃ delta : Int,
      (TransferConservation.aggregate
        (TransferConservation.selectedValues asset (semanticActions openings))
        (TransferConservation.selectedFee asset feeAsset feeAmount) : S) ≠ 0 ∧
      groupSum ((nativeTerms generators openings).map Prod.fst) -
        (feeAmount : Int) • generators feeAsset = delta • blindingGenerator := by
  have semanticBounds : ∀ entry ∈ semanticActions openings, entry.2.natAbs < 2^129 := by
    intro entry present
    obtain ⟨opening, inside, rfl⟩ := List.mem_map.mp present
    exact bounded opening inside
  have nonzero := TransferConservation.selected_nonconservation_has_nonzero_residue
    (S := S) asset feeAsset feeAmount (semanticActions openings)
    (by simpa [semanticActions] using count) semanticBounds feeBound different
  refine ⟨signatureOpening - TransferConservation.signedSum
    ((nativeTerms generators openings).map Prod.snd), nonzero, ?_⟩
  exact extracted_binding_opening_representation (nativeTerms generators openings)
    blindingGenerator (generators feeAsset) feeAmount signatureOpening extracted

/-- Shieldd's separate native input/output group sums agree with the signed
magnitude term once the selected rows establish its exact integer meaning.
Actual point/gadget/scalar APIs must separately refine this group contract;
this lemma makes no commitment-binding or subgroup-membership claim. -/
theorem native_signed_net_agreement {G : Type} [AddCommGroup G]
    (assetGenerator blindingGenerator : G) (blinding : Int)
    (in0 in1 out0 out1 magnitude : Nat) (negative : Bool)
    (signed : (in0 : Int) + (in1 : Int) - (out0 : Int) - (out1 : Int) =
      if negative then -(magnitude : Int) else (magnitude : Int)) :
    ((in0 : Int) + (in1 : Int)) • assetGenerator -
        ((out0 : Int) + (out1 : Int)) • assetGenerator + blinding • blindingGenerator =
      (if negative then -(magnitude : Int) else (magnitude : Int)) • assetGenerator +
        blinding • blindingGenerator := by
  have net : ((in0 : Int) + (in1 : Int)) - ((out0 : Int) + (out1 : Int)) =
      if negative then -(magnitude : Int) else (magnitude : Int) := by
    omega
  calc
    _ = (((in0 : Int) + (in1 : Int)) - ((out0 : Int) + (out1 : Int))) •
        assetGenerator + blinding • blindingGenerator := by
      simpa only [sub_eq_add_neg] using (congrArg
        (fun value : G => value + blinding • blindingGenerator)
        (sub_zsmul assetGenerator ((in0 : Int) + (in1 : Int))
          ((out0 : Int) + (out1 : Int))).symm)
    _ = _ := by rw [net]

set_option pp.all true in
#check @nonconservation_exposes_representation_event
#print axioms nonconservation_exposes_representation_event
set_option pp.all true in
#check @action_commitment_sum
#print axioms action_commitment_sum
set_option pp.all true in
#check @transaction_commitment_decomposition
#print axioms transaction_commitment_decomposition
set_option pp.all true in
#check @extracted_binding_opening_representation
#print axioms extracted_binding_opening_representation
set_option pp.all true in
#check @native_signed_net_agreement
#print axioms native_signed_net_agreement

end ShielddSecurity.TransferBalanceGroup
