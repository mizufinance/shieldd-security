import ShielddSecurity.TransferCommonwareExpBits01
import ShielddSecurity.TransferCommonwareSqrtSchedule01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCommonwareExpField01
open TransferCommonwareExpBits01
open TransferCommonwareSqrtComplete01
open TransferCommonwareSqrtSchedule01
open TransferFfFieldApi01
open TransferBoundedNativeCodec01 (nullifierModulus)
variable {F : Type} [CommMonoid F]

/-- The actual generic monoid_exp recurrence: multiply the accumulator on the
current low bit, then square the cloned running base on every bit. -/
def sourceMonoidExpWalk : List Bool → F → F → F
  | [],acc,_ => acc
  | b::rest,acc,w => sourceMonoidExpWalk rest (if b then acc*w else acc) (w*w)

theorem actual_source_monoid_exp_walk_has_the_exact_little_endian_power
    (bits : List Bool) (acc w : F) :
    sourceMonoidExpWalk bits acc w = acc*w^(bitNumber bits) := by
  induction bits generalizing acc w with
  | nil => simp [sourceMonoidExpWalk,bitNumber]
  | cons bit rest ih =>
    rw [sourceMonoidExpWalk,ih]
    cases bit
    · simp only [Bool.false_eq_true,if_false,bitNumber,Nat.zero_add]
      rw [← pow_two,← pow_mul]
    · simp only [if_true,bitNumber]
      rw [← pow_two,← pow_mul,pow_add,pow_one]
      ac_rfl

def sourceSqrtSeedExp (input : F) : F := sourceMonoidExpWalk sourceSqrtExponentBits 1 input

theorem actual_commonware_sqrt_seed_exp_has_the_locked_integer_power (input : F) :
    sourceSqrtSeedExp input = input ^ TransferScalarWordPrimitives01.packWords sourceCommonwareExponent.toList := by
  rw [sourceSqrtSeedExp,actual_source_monoid_exp_walk_has_the_exact_little_endian_power,
    one_mul,exact_commonware_sqrt_bit_iterator_reconstructs_the_locked_exponent]

local instance scalarPrimeFact : Fact (Nat.Prime nullifierModulus) :=
  ⟨TransferScalarInverseCorrectness01.exact_source_scalar_modulus_is_prime⟩
local instance scalarNonzero : NeZero nullifierModulus := ⟨by decide⟩

def sourceActualInitial (input : TransferCanonicalWordEquality01.CanonicalScalar) :
    FfFinishedPhase296.State (ZMod nullifierModulus) :=
  let value := TransferSqrtProducerField01.sourceFieldValue input
  let r := sourceSqrtSeedExp value
  ⟨r,r*r*value⁻¹,sourceCommonwareRoot,32⟩

theorem actual_commonware_monoid_exp_initialization_derives_the_qualified_producer_state
    (input : TransferCanonicalWordEquality01.CanonicalScalar) : sourceActualInitial input = sourceInitial input := by
  simp only [sourceActualInitial,sourceInitial,actual_commonware_sqrt_seed_exp_has_the_locked_integer_power]

def sourceActualCommonwareSqrt (input : ZMod nullifierModulus) : Option (ZMod nullifierModulus) :=
  if input=0 then some 0 else sourceWhile input (sourceActualInitial (fieldScalar input))

theorem actual_commonware_bit_exp_and_while_producer_agrees_with_the_qualified_field_producer
    (input : ZMod nullifierModulus) : sourceActualCommonwareSqrt input = sourceCommonwareFieldSqrt input := by
  rw [sourceActualCommonwareSqrt,actual_commonware_monoid_exp_initialization_derives_the_qualified_producer_state]
  exact actual_commonware_while_and_budgeted_producers_agree_on_every_input input

theorem actual_commonware_bit_exp_and_while_producer_has_the_total_square_contract (input : ZMod nullifierModulus) :
    (sourceActualCommonwareSqrt input).isSome = true ↔ IsSquare input := by
  rw [actual_commonware_bit_exp_and_while_producer_agrees_with_the_qualified_field_producer]
  exact actual_commonware_source_field_sqrt_has_the_total_square_contract input

set_option pp.all true in
#check @sourceMonoidExpWalk
#print axioms sourceMonoidExpWalk
set_option pp.all true in
#check @actual_source_monoid_exp_walk_has_the_exact_little_endian_power
#print axioms actual_source_monoid_exp_walk_has_the_exact_little_endian_power
set_option pp.all true in
#check @sourceSqrtSeedExp
#print axioms sourceSqrtSeedExp
set_option pp.all true in
#check @actual_commonware_sqrt_seed_exp_has_the_locked_integer_power
#print axioms actual_commonware_sqrt_seed_exp_has_the_locked_integer_power
set_option pp.all true in
#check @scalarPrimeFact
#print axioms scalarPrimeFact
set_option pp.all true in
#check @scalarNonzero
#print axioms scalarNonzero
set_option pp.all true in
#check @sourceActualInitial
#print axioms sourceActualInitial
set_option pp.all true in
#check @actual_commonware_monoid_exp_initialization_derives_the_qualified_producer_state
#print axioms actual_commonware_monoid_exp_initialization_derives_the_qualified_producer_state
set_option pp.all true in
#check @sourceActualCommonwareSqrt
#print axioms sourceActualCommonwareSqrt
set_option pp.all true in
#check @actual_commonware_bit_exp_and_while_producer_agrees_with_the_qualified_field_producer
#print axioms actual_commonware_bit_exp_and_while_producer_agrees_with_the_qualified_field_producer
set_option pp.all true in
#check @actual_commonware_bit_exp_and_while_producer_has_the_total_square_contract
#print axioms actual_commonware_bit_exp_and_while_producer_has_the_total_square_contract
end ShielddSecurity.TransferCommonwareExpField01
