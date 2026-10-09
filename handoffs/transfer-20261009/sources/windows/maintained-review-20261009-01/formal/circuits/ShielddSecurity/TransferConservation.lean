import ShielddSecurity.Scalar
import Mathlib.Data.Int.Basic

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferConservation
open ShielddSecurity

/-- Per-asset selected Transfer coefficients, including an optional Transfer
fee-funding action, are summed as integers. Asset selection and the cryptographic
binding/signature-to-zero-residue contract require separate application joins. -/
def signedSum : List Int → Int
  | [] => 0
  | value :: rest => value + signedSum rest

theorem signed_sum_bound (values : List Int) (bound : Nat)
    (bounded : ∀ value ∈ values, value.natAbs < bound) :
    (signedSum values).natAbs ≤ values.length * bound := by
  induction values with
  | nil => simp [signedSum]
  | cons value rest ih =>
      have head := bounded value (by simp)
      have tail : ∀ x ∈ rest, x.natAbs < bound := by
        intro x present
        exact bounded x (by simp [present])
      have triangle := Int.natAbs_add_le value (signedSum rest)
      have total := Nat.add_le_add (Nat.le_of_lt head) (ih tail)
      exact triangle.trans (by simpa [signedSum, Nat.succ_mul, Nat.add_comm] using total)

def aggregate (values : List Int) (fee : Nat) : Int := signedSum values - (fee : Int)

theorem aggregate_bound (values : List Int) (fee : Nat)
    (count : values.length ≤ 512)
    (bounded : ∀ value ∈ values, value.natAbs < 2^129)
    (feeBound : fee < 2^128) :
    (aggregate values fee).natAbs < 512 * 2^129 + 2^128 := by
  have sumBound := (signed_sum_bound values (2^129) bounded).trans
    (Nat.mul_le_mul_right (2^129) count)
  have triangle := Int.natAbs_add_le (signedSum values) (-(fee : Int))
  have total : (aggregate values fee).natAbs ≤ 512 * 2^129 + fee := by
    have cleaned : (aggregate values fee).natAbs ≤ (signedSum values).natAbs + fee := by
      simpa [aggregate, sub_eq_add_neg] using triangle
    exact cleaned.trans (Nat.add_le_add_right sumBound fee)
  exact total.trans_lt (Nat.add_lt_add_left feeBound _)

theorem aggregate_capacity : 512 * 2^129 + 2^128 < Scalar.order := by decide

/-- The zero residue is a cryptographic application contract, not a consequence
of additive-group algebra or universal independence of asset generators. -/
theorem bounded_zero_residue {S : Type} [Field S] [CharP S Scalar.order]
    (value : Int) (bound : value.natAbs < Scalar.order)
    (zeroResidue : (value : S) = 0) : value = 0 := by
  cases value with
  | ofNat n =>
      have bounded : n < Scalar.order := by simpa using bound
      have zero : (n : S) = (0 : Nat) := by simpa using zeroResidue
      have eq := bounded_cast_injective (F := S) (p := Scalar.order) bounded
        (by decide : 0 < Scalar.order) zero
      simpa using congrArg Int.ofNat eq
  | negSucc n =>
      have bounded : n + 1 < Scalar.order := by simpa using bound
      have zero : ((n + 1 : Nat) : S) = 0 := by
        have negative : -(((n + 1 : Nat) : S)) = 0 := by simpa using zeroResidue
        exact neg_eq_zero.mp negative
      have impossible := bounded_cast_injective (F := S) (p := Scalar.order) bounded
        (by decide : 0 < Scalar.order) (by simpa using zero)
      omega

theorem transfer_only_per_asset_conservation {S : Type} [Field S] [CharP S Scalar.order]
    (values : List Int) (fee : Nat) (count : values.length ≤ 512)
    (bounded : ∀ value ∈ values, value.natAbs < 2^129)
    (feeBound : fee < 2^128) (zeroResidue : (aggregate values fee : S) = 0) :
    signedSum values = (fee : Int) := by
  have capacity := (aggregate_bound values fee count bounded feeBound).trans aggregate_capacity
  have zero := bounded_zero_residue (S := S) (aggregate values fee) capacity zeroResidue
  exact sub_eq_zero.mp zero

/-- Semantic coefficients extracted under the proof contract from one body plus
optional fee-funding list. This is not a claim that assets are public fields. -/
def selectedValues (asset : Nat) (allActions : List (Nat × Int)) : List Int :=
  (allActions.filter (fun entry => entry.1 == asset)).map Prod.snd

def selectedFee (asset feeAsset feeAmount : Nat) : Nat :=
  if asset = feeAsset then feeAmount else 0

/-- Preserve every action occurrence, including equal commitments or equal
assets. The optional fee-funding Transfer contributes once, in addition to the
public negative fee term; it is not the fee itself. -/
def completeActions (body : List (Nat × Int)) (feeFunding : Option (Nat × Int)) :
    List (Nat × Int) := body ++ feeFunding.toList

theorem signed_sum_append (left right : List Int) :
    signedSum (left ++ right) = signedSum left + signedSum right := by
  induction left with
  | nil => simp [signedSum]
  | cons head tail ih => simp [signedSum, ih, add_assoc]

theorem selected_values_append (asset : Nat) (left right : List (Nat × Int)) :
    selectedValues asset (left ++ right) = selectedValues asset left ++ selectedValues asset right := by
  simp only [selectedValues, List.filter_append, List.map_append]

theorem selected_singleton (asset entryAsset : Nat) (value : Int) :
    signedSum (selectedValues asset [(entryAsset, value)]) =
      if entryAsset = asset then value else 0 := by
  by_cases same : entryAsset = asset <;> simp [selectedValues, signedSum, same]

theorem optional_fee_funding_once (asset : Nat) (body : List (Nat × Int))
    (feeFunding : Option (Nat × Int)) :
    signedSum (selectedValues asset (completeActions body feeFunding)) =
      signedSum (selectedValues asset body) +
        match feeFunding with
        | none => 0
        | some entry => if entry.1 = asset then entry.2 else 0 := by
  rw [completeActions, selected_values_append, signed_sum_append]
  cases feeFunding with
  | none => simp [selectedValues, signedSum]
  | some entry =>
      simpa using congrArg (fun value : Int => signedSum (selectedValues asset body) + value)
        (selected_singleton asset entry.1 entry.2)

theorem complete_action_count (body : List (Nat × Int)) (feeFunding : Option (Nat × Int))
    (count : body.length + feeFunding.toList.length ≤ 512) :
    (completeActions body feeFunding).length ≤ 512 := by
  simpa [completeActions] using count

/-- Repeated selected occurrences retain multiplicity; a set-based aggregate
would lose this second contribution. -/
theorem duplicate_action_counted_twice (asset : Nat) (value : Int) :
    signedSum (selectedValues asset [(asset, value), (asset, value)]) = value + value := by
  simp [selectedValues, signedSum]

/-- pay_fee partitions the same public base-asset fee into base and proposer
tip before retaining it. Store overflow/durability refinement is separate. -/
theorem retained_fee_partition (fee baseFee : Nat) (minimum : baseFee ≤ fee) :
    baseFee + (fee - baseFee) = fee := by omega

theorem selected_fee_bound (asset feeAsset feeAmount : Nat) (feeBound : feeAmount < 2^128) :
    selectedFee asset feeAsset feeAmount < 2^128 := by
  by_cases same : asset = feeAsset
  · simpa [selectedFee, same] using feeBound
  · simp [selectedFee, same]

theorem selected_action_bounds (asset : Nat) (allActions : List (Nat × Int))
    (count : allActions.length ≤ 512)
    (bounded : ∀ entry ∈ allActions, entry.2.natAbs < 2^129) :
    (selectedValues asset allActions).length ≤ 512 ∧
      ∀ value ∈ selectedValues asset allActions, value.natAbs < 2^129 := by
  constructor
  · have filtered := List.length_filter_le (fun entry : Nat × Int => entry.1 == asset) allActions
    simpa only [selectedValues, List.length_map] using filtered.trans count
  · intro value present
    obtain ⟨entry, filtered, same⟩ := List.mem_map.mp present
    have inside := (List.mem_filter.mp filtered).1
    subst value
    exact bounded entry inside

/-- Per-asset fee selection and action count come from the same complete
Transfer-only body plus optional Transfer fee-funding semantic witness list.
The zero residue still requires computational binding/knowledge and application
extraction contracts; no universal generator independence is asserted. -/
theorem selected_asset_conservation {S : Type} [Field S] [CharP S Scalar.order]
    (asset feeAsset feeAmount : Nat) (allActions : List (Nat × Int))
    (count : allActions.length ≤ 512)
    (bounded : ∀ entry ∈ allActions, entry.2.natAbs < 2^129)
    (feeBound : feeAmount < 2^128)
    (zeroResidue : (aggregate (selectedValues asset allActions)
      (selectedFee asset feeAsset feeAmount) : S) = 0) :
    signedSum (selectedValues asset allActions) = (selectedFee asset feeAsset feeAmount : Int) := by
  obtain ⟨selectedCount, selectedBounds⟩ := selected_action_bounds asset allActions count bounded
  exact transfer_only_per_asset_conservation _ _ selectedCount selectedBounds
    (selected_fee_bound asset feeAsset feeAmount feeBound) zeroResidue

/-- A violating extracted semantic witness has a nonzero scalar coefficient;
the explicit transaction bound prevents cancellation by wrapping modulo the
group order. A binding reduction must exclude this bad opening computationally,
rather than postulate conservation or generator independence. -/
theorem selected_nonconservation_has_nonzero_residue {S : Type} [Field S] [CharP S Scalar.order]
    (asset feeAsset feeAmount : Nat) (allActions : List (Nat × Int))
    (count : allActions.length ≤ 512)
    (bounded : ∀ entry ∈ allActions, entry.2.natAbs < 2^129)
    (feeBound : feeAmount < 2^128)
    (different : signedSum (selectedValues asset allActions) ≠
      (selectedFee asset feeAsset feeAmount : Int)) :
    (aggregate (selectedValues asset allActions) (selectedFee asset feeAsset feeAmount) : S) ≠ 0 := by
  intro zero
  exact different (selected_asset_conservation (S := S) asset feeAsset feeAmount allActions
    count bounded feeBound zero)

set_option pp.all true in
#check @selected_nonconservation_has_nonzero_residue
#print axioms selected_nonconservation_has_nonzero_residue
set_option pp.all true in
#check @retained_fee_partition
#print axioms retained_fee_partition
set_option pp.all true in
#check @signed_sum_append
#print axioms signed_sum_append
set_option pp.all true in
#check @selected_values_append
#print axioms selected_values_append
set_option pp.all true in
#check @selected_singleton
#print axioms selected_singleton
set_option pp.all true in
#check @optional_fee_funding_once
#print axioms optional_fee_funding_once
set_option pp.all true in
#check @complete_action_count
#print axioms complete_action_count
set_option pp.all true in
#check @duplicate_action_counted_twice
#print axioms duplicate_action_counted_twice
set_option pp.all true in
#check @selected_fee_bound
#print axioms selected_fee_bound
set_option pp.all true in
#check @selected_action_bounds
#print axioms selected_action_bounds
set_option pp.all true in
#check @selected_asset_conservation
#print axioms selected_asset_conservation

set_option pp.all true in
#check @signed_sum_bound
#print axioms signed_sum_bound
set_option pp.all true in
#check @aggregate_bound
#print axioms aggregate_bound
set_option pp.all true in
#check @aggregate_capacity
#print axioms aggregate_capacity
set_option pp.all true in
#check @bounded_zero_residue
#print axioms bounded_zero_residue
set_option pp.all true in
#check @transfer_only_per_asset_conservation
#print axioms transfer_only_per_asset_conservation

end ShielddSecurity.TransferConservation
