import ShielddSecurity.TransferCommonwareMapParameters01
import ShielddSecurity.TransferCommonwareSqrtSchedule01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
noncomputable section
namespace ShielddSecurity.TransferCommonwareMapCaller01
attribute [local irreducible] TransferFfFieldApi01.sourceSdkFieldSqrt
  TransferCommonwareMapRoots01.sdkRootProgram TransferCommonwareMapRoots01.sdkRootOption
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferCommonwareMapRoots01
open TransferCommonwareMapParameters01
open TransferCommonwareSqrtComplete01
open TransferCommonwareSqrtSchedule01
open TransferFfFieldApi01
local instance scalarPrimeFact : Fact (Nat.Prime nullifierModulus) :=
  ⟨TransferScalarInverseCorrectness01.exact_source_scalar_modulus_is_prime⟩
local instance scalarNonzero : NeZero nullifierModulus := ⟨by decide⟩

theorem actual_normalized_root_preserves_the_computed_square
    (choice : Bool) (root : ZMod nullifierModulus) :
    normalizeRoot choice root * normalizeRoot choice root = root*root := by
  unfold normalizeRoot
  split_ifs
  all_goals first | rfl | exact neg_mul_neg _ _

theorem actual_normalized_root_derives_canonical_parity (choice : Bool) (root : ZMod nullifierModulus)
    (zeroChoice : root=0 → choice=false) :
    (normalizeRoot choice root).val % 2 = if choice then 1 else 0 := by
  by_cases zero : root=0
  · have chosen := zeroChoice zero
    simp [zero,chosen,normalizeRoot]
  · by_cases same : root.val % 2 = (if choice then 1 else 0)
    · simpa only [normalizeRoot,if_pos same] using same
    · simp only [normalizeRoot,if_neg same,ZMod.neg_val,if_neg zero]
      have bounded := root.val_lt
      have positive : 0 < root.val := by
        by_contra absent
        exact zero ((ZMod.val_eq_zero root).mp (by omega))
      have odd : nullifierModulus % 2 = 1 := by decide
      cases choice <;> simp only [Bool.false_eq_true,if_false,if_true] at same ⊢ <;> omega

theorem every_computed_commonware_root_program_success_derives_the_selected_square
    (first alternative root : ZMod nullifierModulus) (success : commonwareRootProgram first alternative = some root) :
    root*root = if (sourceCommonwareFieldSqrt first).isSome then first else alternative := by
  let choice := (sourceCommonwareFieldSqrt first).isSome
  let value := if choice then first else alternative
  have option : commonwareRootOption first alternative = sourceCommonwareFieldSqrt value := by
    unfold commonwareRootOption value choice
    split <;> rfl
  rw [commonwareRootProgram,option] at success
  cases observed : sourceCommonwareFieldSqrt value with
  | none => simp only [observed,Option.map_none,reduceCtorEq] at success
  | some raw =>
    have same : normalizeRoot choice raw = root := by
      simpa only [observed,Option.map_some,Option.some.injEq] using success
    rw [← same,actual_normalized_root_preserves_the_computed_square]
    exact actual_commonware_source_field_sqrt_is_sound value raw observed

def sourceAlternative (u : ZMod nullifierModulus) : ZMod nullifierModulus := 5*u*u*sourceFirstCubic u
def sourceChoice (u : ZMod nullifierModulus) : Bool := (sourceCommonwareFieldSqrt (sourceFirstCubic u)).isSome
def sourceSelectedX (u : ZMod nullifierModulus) : ZMod nullifierModulus :=
  if sourceChoice u then sourceFirstX u else -sourceFirstX u-sourceC1
def sourceSdkSelectedX (u : ZMod nullifierModulus) : ZMod nullifierModulus :=
  if (sourceSdkFieldSqrt (sourceFirstCubic u)).isSome then sourceFirstX u else -sourceFirstX u-sourceC1
theorem actual_source_sdk_and_commonware_x_choices_agree (u : ZMod nullifierModulus) :
    sourceSdkSelectedX u = sourceSelectedX u := by
  unfold sourceSdkSelectedX sourceSelectedX sourceChoice
  rw [actual_sdk_and_commonware_square_choices_agree]
def sourceSelectedRoot (u : ZMod nullifierModulus) : ZMod nullifierModulus :=
  (commonwareRootProgram (sourceFirstCubic u) (sourceAlternative u)).getD 0

theorem actual_map_root_constructor_derives_option_square_and_parity (u : ZMod nullifierModulus) :
    commonwareRootProgram (sourceFirstCubic u) (sourceAlternative u) = some (sourceSelectedRoot u) ∧
    sourceSelectedRoot u * sourceSelectedRoot u =
      (if sourceChoice u then sourceFirstCubic u else sourceAlternative u) ∧
    (sourceSelectedRoot u).val % 2 = if sourceChoice u then 1 else 0 := by
  obtain ⟨root,_,available⟩ := actual_elligator_selected_normalized_root_programs_are_available u (sourceFirstCubic u)
  have returned : commonwareRootProgram (sourceFirstCubic u) (sourceAlternative u) = some (sourceSelectedRoot u) := by
    have same : sourceSelectedRoot u = root := by
      simp only [sourceSelectedRoot,sourceAlternative,available,Option.getD_some]
    rw [same]
    exact available
  have row := every_computed_commonware_root_program_success_derives_the_selected_square _ _ _ returned
  change sourceSelectedRoot u * sourceSelectedRoot u =
    (if sourceChoice u then sourceFirstCubic u else sourceAlternative u) at row
  refine ⟨returned,row,?_⟩
  unfold sourceSelectedRoot commonwareRootProgram
  cases observed : commonwareRootOption (sourceFirstCubic u) (sourceAlternative u) with
  | none => simp only [commonwareRootProgram,observed,Option.map_none,reduceCtorEq] at returned
  | some raw =>
    simp only [Option.map_some,Option.getD_some]
    change (normalizeRoot (sourceChoice u) raw).val % 2 = if sourceChoice u then 1 else 0
    apply actual_normalized_root_derives_canonical_parity
    intro zero
    cases chosen : sourceChoice u with
    | false => rfl
    | true =>
      have rootZero : sourceSelectedRoot u = 0 := by
        simp only [sourceSelectedRoot,commonwareRootProgram,observed,Option.map_some,Option.getD_some,zero,normalizeRoot,neg_zero,ite_self]
      have firstZero : (0 : ZMod nullifierModulus) = sourceFirstCubic u := by
        simpa only [chosen,if_true,rootZero,zero_mul] using row
      exact False.elim (actual_elligator_first_cubic_is_nonzero u firstZero.symm)

def sdkRationalInput (x y : ZMod nullifierModulus) : ZMod nullifierModulus × ZMod nullifierModulus :=
  let s := x*sourceK
  let t := y*sourceK
  let plus := s+1
  let denominator := plus*t
  let inverse := denominator⁻¹
  (inverse*plus*s,if denominator=0 then 1 else inverse*t*(s-1))

def commonwareRationalInput (x y : ZMod nullifierModulus) : ZMod nullifierModulus × ZMod nullifierModulus :=
  let s := x*sourceK
  let t := y*sourceK
  let plus := s+1
  let denominator := plus*t
  if denominator=0 then (0,1) else (denominator⁻¹*plus*s,denominator⁻¹*t*(s-1))

theorem actual_sdk_and_commonware_rational_map_inputs_agree (x y : ZMod nullifierModulus) :
    sdkRationalInput x y = commonwareRationalInput x y := by
  unfold sdkRationalInput commonwareRationalInput
  dsimp only
  by_cases zero : (x*sourceK+1)*(y*sourceK)=0
  · simp [zero]
  · simp only [if_neg zero]

def sourceSdkCofactorInput (u : ZMod nullifierModulus) : ZMod nullifierModulus × ZMod nullifierModulus :=
  sdkRationalInput (sourceSdkSelectedX u)
    (sourceSelectedRoot u)

theorem actual_sdk_root_program_returns_the_independently_computed_selected_root (u : ZMod nullifierModulus) :
    sdkRootProgram (sourceFirstCubic u) (sourceAlternative u) = some (sourceSelectedRoot u) := by
  rw [actual_sdk_and_commonware_selected_normalized_root_programs_agree]
  exact (actual_map_root_constructor_derives_option_square_and_parity u).1

theorem actual_sdk_cofactor_input_is_its_actual_option_program_payload (u : ZMod nullifierModulus) :
    (sdkRootProgram (sourceFirstCubic u) (sourceAlternative u)).map (sdkRationalInput (sourceSdkSelectedX u)) =
      some (sourceSdkCofactorInput u) := by
  rw [actual_sdk_root_program_returns_the_independently_computed_selected_root,Option.map_some]
  rfl

def sourceCommonwareCofactorInput (u : ZMod nullifierModulus) : Option (ZMod nullifierModulus × ZMod nullifierModulus) :=
  (commonwareRootProgram (sourceFirstCubic u) (sourceAlternative u)).map
    (commonwareRationalInput (sourceSelectedX u))

theorem actual_source_map_callers_derive_the_same_cofactor_input (u : ZMod nullifierModulus) :
    sourceCommonwareCofactorInput u = some (sourceSdkCofactorInput u) := by
  have available := (actual_map_root_constructor_derives_option_square_and_parity u).1
  unfold sourceCommonwareCofactorInput sourceSdkCofactorInput
  rw [actual_source_sdk_and_commonware_x_choices_agree]
  rw [available]
  simp only [Option.map_some,actual_sdk_and_commonware_rational_map_inputs_agree]

theorem actual_source_map_cofactor_input_is_preserved_by_every_common_cofactor_program
    {O : Type} (cofactor : (ZMod nullifierModulus × ZMod nullifierModulus) → O) (u : ZMod nullifierModulus) :
    (sourceCommonwareCofactorInput u).map cofactor = some (cofactor (sourceSdkCofactorInput u)) := by
  rw [actual_source_map_callers_derive_the_same_cofactor_input,Option.map_some]

theorem actual_commonware_while_sqrt_is_the_same_selected_caller_operation (input : ZMod nullifierModulus) :
    sourceCommonwareWhileSqrt input = sourceCommonwareFieldSqrt input :=
  actual_commonware_while_and_budgeted_producers_agree_on_every_input input

set_option pp.all true in
#check @scalarPrimeFact
#print axioms scalarPrimeFact
set_option pp.all true in
#check @scalarNonzero
#print axioms scalarNonzero
set_option pp.all true in
#check @actual_normalized_root_preserves_the_computed_square
#print axioms actual_normalized_root_preserves_the_computed_square
set_option pp.all true in
#check @actual_normalized_root_derives_canonical_parity
#print axioms actual_normalized_root_derives_canonical_parity
set_option pp.all true in
#check @every_computed_commonware_root_program_success_derives_the_selected_square
#print axioms every_computed_commonware_root_program_success_derives_the_selected_square
set_option pp.all true in
#check @sourceAlternative
#print axioms sourceAlternative
set_option pp.all true in
#check @sourceChoice
#print axioms sourceChoice
set_option pp.all true in
#check @sourceSelectedX
#print axioms sourceSelectedX
set_option pp.all true in
#check @sourceSdkSelectedX
#print axioms sourceSdkSelectedX
set_option pp.all true in
#check @actual_source_sdk_and_commonware_x_choices_agree
#print axioms actual_source_sdk_and_commonware_x_choices_agree
set_option pp.all true in
#check @sourceSelectedRoot
#print axioms sourceSelectedRoot
set_option pp.all true in
#check @actual_map_root_constructor_derives_option_square_and_parity
#print axioms actual_map_root_constructor_derives_option_square_and_parity
set_option pp.all true in
#check @sdkRationalInput
#print axioms sdkRationalInput
set_option pp.all true in
#check @commonwareRationalInput
#print axioms commonwareRationalInput
set_option pp.all true in
#check @actual_sdk_and_commonware_rational_map_inputs_agree
#print axioms actual_sdk_and_commonware_rational_map_inputs_agree
set_option pp.all true in
#check @sourceSdkCofactorInput
#print axioms sourceSdkCofactorInput
set_option pp.all true in
#check @actual_sdk_root_program_returns_the_independently_computed_selected_root
#print axioms actual_sdk_root_program_returns_the_independently_computed_selected_root
set_option pp.all true in
#check @actual_sdk_cofactor_input_is_its_actual_option_program_payload
#print axioms actual_sdk_cofactor_input_is_its_actual_option_program_payload
set_option pp.all true in
#check @sourceCommonwareCofactorInput
#print axioms sourceCommonwareCofactorInput
set_option pp.all true in
#check @actual_source_map_callers_derive_the_same_cofactor_input
#print axioms actual_source_map_callers_derive_the_same_cofactor_input
set_option pp.all true in
#check @actual_source_map_cofactor_input_is_preserved_by_every_common_cofactor_program
#print axioms actual_source_map_cofactor_input_is_preserved_by_every_common_cofactor_program
set_option pp.all true in
#check @actual_commonware_while_sqrt_is_the_same_selected_caller_operation
#print axioms actual_commonware_while_sqrt_is_the_same_selected_caller_operation
end ShielddSecurity.TransferCommonwareMapCaller01
