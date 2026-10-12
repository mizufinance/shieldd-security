import ShielddSecurity.TransferCommonwareSqrtComplete01
import ShielddSecurity.TransferFfEulerCriterion01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCommonwareMapRoots01
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferFfFieldApi01
open TransferFfEulerCriterion01
open TransferCommonwareSqrtComplete01
local instance scalarPrimeFact : Fact (Nat.Prime nullifierModulus) :=
  ⟨TransferScalarInverseCorrectness01.exact_source_scalar_modulus_is_prime⟩
local instance scalarNonzero : NeZero nullifierModulus := ⟨by decide⟩

def normalizeRoot (choice : Bool) (root : ZMod nullifierModulus) : ZMod nullifierModulus :=
  if root.val % 2 = (if choice then 1 else 0) then root else -root

theorem exact_canonical_negation_flips_nonzero_parity (root : ZMod nullifierModulus) (nonzero : root ≠ 0) :
    (-root).val % 2 ≠ root.val % 2 := by
  rw [ZMod.neg_val,if_neg nonzero]
  have bounded := root.val_lt
  have positive : 0 < root.val := by
    by_contra absent
    exact nonzero ((ZMod.val_eq_zero root).mp (by omega))
  have odd : nullifierModulus % 2 = 1 := by decide
  omega

theorem actual_canonical_sign_normalization_agrees_on_opposite_roots
    (choice : Bool) (root : ZMod nullifierModulus) : normalizeRoot choice (-root) = normalizeRoot choice root := by
  by_cases zero : root = 0
  · simp [zero,normalizeRoot]
  · have flip := exact_canonical_negation_flips_nonzero_parity root zero
    have bounded : root.val % 2 < 2 := Nat.mod_lt _ (by decide)
    have negBound : (-root).val % 2 < 2 := Nat.mod_lt _ (by decide)
    cases choice <;> unfold normalizeRoot <;>
      simp only [Bool.false_eq_true,if_false,if_true] <;>
      split_ifs
    all_goals first | rfl | exact neg_neg root | omega

theorem equal_squares_derive_equal_actual_normalized_roots (choice : Bool)
    (left right : ZMod nullifierModulus) (squares : left*left = right*right) :
    normalizeRoot choice left = normalizeRoot choice right := by
  have factors : (left-right)*(left+right) = 0 := by
    calc
      _ = left*left-right*right := by ring
      _ = 0 := by rw [squares,sub_self]
  rcases mul_eq_zero.mp factors with same | opposite
  · rw [sub_eq_zero.mp same]
  · rw [eq_neg_of_add_eq_zero_left opposite]
    exact actual_canonical_sign_normalization_agrees_on_opposite_roots choice right

theorem actual_sdk_and_commonware_square_choices_agree (input : ZMod nullifierModulus) :
    (sourceSdkFieldSqrt input).isSome = (sourceCommonwareFieldSqrt input).isSome := by
  have equivalent := (actual_source_sdk_field_sqrt_has_the_total_square_contract input).trans
    (actual_commonware_source_field_sqrt_has_the_total_square_contract input).symm
  cases sdk : (sourceSdkFieldSqrt input).isSome <;>
    cases commonware : (sourceCommonwareFieldSqrt input).isSome <;> simp_all

theorem actual_sdk_and_commonware_normalized_sqrt_options_agree
    (input : ZMod nullifierModulus) (choice : Bool) :
    (sourceSdkFieldSqrt input).map (normalizeRoot choice) =
      (sourceCommonwareFieldSqrt input).map (normalizeRoot choice) := by
  have sameChoice := actual_sdk_and_commonware_square_choices_agree input
  cases sdk : sourceSdkFieldSqrt input with
  | none =>
    cases commonware : sourceCommonwareFieldSqrt input with
    | none => rfl
    | some root => simp only [sdk,commonware,Option.isSome_none,Option.isSome_some,Bool.false_eq_true] at sameChoice
  | some left =>
    cases commonware : sourceCommonwareFieldSqrt input with
    | none => simp only [sdk,commonware,Option.isSome_none,Option.isSome_some,Bool.true_eq_false] at sameChoice
    | some right =>
      simp only [Option.map_some,Option.some.injEq]
      exact equal_squares_derive_equal_actual_normalized_roots choice left right
        ((actual_source_sdk_field_sqrt_is_sound input left sdk).trans
          (actual_commonware_source_field_sqrt_is_sound input right commonware).symm)

def sdkRootOption (first alternative : ZMod nullifierModulus) : Option (ZMod nullifierModulus) :=
  if (sourceSdkFieldSqrt first).isSome then sourceSdkFieldSqrt first else sourceSdkFieldSqrt alternative

def commonwareRootOption (first alternative : ZMod nullifierModulus) : Option (ZMod nullifierModulus) :=
  if (sourceCommonwareFieldSqrt first).isSome then sourceCommonwareFieldSqrt first else sourceCommonwareFieldSqrt alternative

def sdkRootProgram (first alternative : ZMod nullifierModulus) : Option (ZMod nullifierModulus) :=
  (sdkRootOption first alternative).map (normalizeRoot (sourceSdkFieldSqrt first).isSome)

def commonwareRootProgram (first alternative : ZMod nullifierModulus) : Option (ZMod nullifierModulus) :=
  (commonwareRootOption first alternative).map (normalizeRoot (sourceCommonwareFieldSqrt first).isSome)

theorem actual_sdk_and_commonware_selected_normalized_root_programs_agree
    (first alternative : ZMod nullifierModulus) : sdkRootProgram first alternative = commonwareRootProgram first alternative := by
  have same := actual_sdk_and_commonware_square_choices_agree first
  unfold sdkRootProgram commonwareRootProgram sdkRootOption commonwareRootOption
  rw [same]
  cases choice : (sourceCommonwareFieldSqrt first).isSome <;>
    simp only [Bool.false_eq_true,if_false,if_true]
  · exact actual_sdk_and_commonware_normalized_sqrt_options_agree alternative false
  · exact actual_sdk_and_commonware_normalized_sqrt_options_agree first true

theorem exact_elligator_five_parameter_has_negative_euler_power :
    (5 : ZMod nullifierModulus) ^ (nullifierModulus/2) = -1 := by
  have power : (ModularPower.power nullifierModulus 5 (nullifierModulus/2) : ZMod nullifierModulus) =
      (5 : ZMod nullifierModulus) ^ (nullifierModulus/2) := by
    simpa only [Nat.cast_ofNat] using ModularPower.power_sound nullifierModulus 5 (nullifierModulus/2)
  rw [← power]
  have checked : ModularPower.power nullifierModulus 5 (nullifierModulus/2) = nullifierModulus-1 := by decide +kernel
  rw [checked,Nat.cast_sub (by decide : 1 ≤ nullifierModulus),ZMod.natCast_self,Nat.cast_one,zero_sub]

def selectedValue (u first : ZMod nullifierModulus) : ZMod nullifierModulus :=
  if (sourceCommonwareFieldSqrt first).isSome then first else 5*u*u*first

theorem actual_elligator_selected_value_is_square (u first : ZMod nullifierModulus) : IsSquare (selectedValue u first) := by
  by_cases chosen : (sourceCommonwareFieldSqrt first).isSome = true
  · simpa only [selectedValue,if_pos chosen] using (actual_commonware_source_field_sqrt_has_the_total_square_contract first).mp chosen
  · have nonsquare : ¬ IsSquare first := fun square => chosen
      ((actual_commonware_source_field_sqrt_has_the_total_square_contract first).mpr square)
    have negative := every_nonsquare_has_negative_euler_power first nonsquare
    have alternativeSquare : IsSquare ((5 : ZMod nullifierModulus)*first) := by
      apply actual_ff_order_progress_derives_a_root_from_positive_euler_power
      rw [mul_pow,exact_elligator_five_parameter_has_negative_euler_power,negative]
      ring
    obtain ⟨root,equation⟩ := alternativeSquare
    refine ⟨u*root,?_⟩
    simp only [selectedValue,if_neg chosen]
    calc
      5*u*u*first = u*u*(5*first) := by ring
      _ = (u*root)*(u*root) := by rw [equation]; ring

theorem actual_elligator_selected_normalized_root_programs_are_available (u first : ZMod nullifierModulus) :
    ∃ root, sdkRootProgram first (5*u*u*first) = some root ∧ commonwareRootProgram first (5*u*u*first) = some root := by
  have square := actual_elligator_selected_value_is_square u first
  obtain ⟨root,success⟩ := actual_commonware_source_field_sqrt_is_complete (selectedValue u first) square
  have option : commonwareRootOption first (5*u*u*first) = sourceCommonwareFieldSqrt (selectedValue u first) := by
    unfold commonwareRootOption selectedValue
    split <;> rfl
  have available : commonwareRootProgram first (5*u*u*first) =
      some (normalizeRoot (sourceCommonwareFieldSqrt first).isSome root) := by
    simp only [commonwareRootProgram,option,success,Option.map_some]
  exact ⟨_,(actual_sdk_and_commonware_selected_normalized_root_programs_agree _ _).trans available,available⟩

set_option pp.all true in
#check @scalarPrimeFact
#print axioms scalarPrimeFact
set_option pp.all true in
#check @scalarNonzero
#print axioms scalarNonzero
set_option pp.all true in
#check @normalizeRoot
#print axioms normalizeRoot
set_option pp.all true in
#check @exact_canonical_negation_flips_nonzero_parity
#print axioms exact_canonical_negation_flips_nonzero_parity
set_option pp.all true in
#check @actual_canonical_sign_normalization_agrees_on_opposite_roots
#print axioms actual_canonical_sign_normalization_agrees_on_opposite_roots
set_option pp.all true in
#check @equal_squares_derive_equal_actual_normalized_roots
#print axioms equal_squares_derive_equal_actual_normalized_roots
set_option pp.all true in
#check @actual_sdk_and_commonware_square_choices_agree
#print axioms actual_sdk_and_commonware_square_choices_agree
set_option pp.all true in
#check @actual_sdk_and_commonware_normalized_sqrt_options_agree
#print axioms actual_sdk_and_commonware_normalized_sqrt_options_agree
set_option pp.all true in
#check @sdkRootOption
#print axioms sdkRootOption
set_option pp.all true in
#check @commonwareRootOption
#print axioms commonwareRootOption
set_option pp.all true in
#check @sdkRootProgram
#print axioms sdkRootProgram
set_option pp.all true in
#check @commonwareRootProgram
#print axioms commonwareRootProgram
set_option pp.all true in
#check @actual_sdk_and_commonware_selected_normalized_root_programs_agree
#print axioms actual_sdk_and_commonware_selected_normalized_root_programs_agree
set_option pp.all true in
#check @exact_elligator_five_parameter_has_negative_euler_power
#print axioms exact_elligator_five_parameter_has_negative_euler_power
set_option pp.all true in
#check @selectedValue
#print axioms selectedValue
set_option pp.all true in
#check @actual_elligator_selected_value_is_square
#print axioms actual_elligator_selected_value_is_square
set_option pp.all true in
#check @actual_elligator_selected_normalized_root_programs_are_available
#print axioms actual_elligator_selected_normalized_root_programs_are_available
end ShielddSecurity.TransferCommonwareMapRoots01
