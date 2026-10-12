import ShielddSecurity.TransferScalarFieldValues01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarInvertField01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferScalarInvertMachine01
open TransferScalarInvertChain01
open TransferScalarFieldValues01

/-! A symbolic simulation connects the actual modeled Montgomery register
machine with its parallel natural-exponent machine. The source instruction
certificate supplies the exponent; no desired field-value conclusion is an
input premise. Primality/Fermat and native caller/compiler binding are separate. -/

def registersCorrespond (self : CanonicalScalar) (state : RegisterState)
    (exponents : Nat → Option Nat) : Prop :=
  ∀ index, (state index).map (fun value => montgomeryValue value.words) =
    (exponents index).map (fun exponent => montgomeryValue self.words ^ exponent % nullifierModulus)

theorem corresponding_registers_derive_corresponding_operand_values
    (self : CanonicalScalar) (state : RegisterState) (exponents : Nat → Option Nat)
    (operand : InvertOperand) (correspond : registersCorrespond self state exponents) :
    (sourceOperand self state operand).map (fun value => montgomeryValue value.words) =
      (sourceExponentOperand exponents operand).map
        (fun exponent => montgomeryValue self.words ^ exponent % nullifierModulus) := by
  cases operand with
  | input =>
    change some (montgomeryValue self.words) = some (montgomeryValue self.words ^ 1 % nullifierModulus)
    rw [Nat.pow_one]
    unfold montgomeryValue
    rw [Nat.mod_mod]
  | register index => exact correspond index

theorem successful_corresponding_source_operand_derives_exact_exponent_read
    (self : CanonicalScalar) (state : RegisterState) (exponents : Nat → Option Nat)
    (operand : InvertOperand) (value : CanonicalScalar)
    (correspond : registersCorrespond self state exponents)
    (returned : sourceOperand self state operand = some value) :
    ∃ exponent, sourceExponentOperand exponents operand = some exponent ∧
      montgomeryValue value.words = montgomeryValue self.words ^ exponent % nullifierModulus := by
  have mapped := corresponding_registers_derive_corresponding_operand_values self state exponents operand correspond
  rw [returned] at mapped
  cases read : sourceExponentOperand exponents operand with
  | none =>
    rw [read] at mapped
    cases mapped
  | some exponent =>
    refine ⟨exponent, read, ?_⟩
    rw [read] at mapped
    exact Option.some.inj mapped

theorem matching_register_updates_preserve_field_exponent_correspondence
    (self : CanonicalScalar) (state : RegisterState) (exponents : Nat → Option Nat)
    (target : Nat) (value : CanonicalScalar) (exponent : Nat)
    (correspond : registersCorrespond self state exponents)
    (valueEquation : montgomeryValue value.words = montgomeryValue self.words ^ exponent % nullifierModulus) :
    registersCorrespond self (sourceRegisterPut state target value)
      (fun index => if index = target then some exponent else exponents index) := by
  intro index
  by_cases same : index = target
  · simp only [sourceRegisterPut, if_pos same, Option.map_some, valueEquation]
  · simp only [sourceRegisterPut, if_neg same]
    exact correspond index

theorem successful_source_instruction_derives_matching_exponent_instruction
    (self : CanonicalScalar) (state updated : RegisterState) (exponents : Nat → Option Nat)
    (instruction : InvertInstruction) (correspond : registersCorrespond self state exponents)
    (returned : sourceApply self state instruction = some updated) :
    ∃ nextExponents, sourceExponentApply exponents instruction = some nextExponents ∧
      registersCorrespond self updated nextExponents := by
  cases instruction with
  | square target operand count =>
    change (sourceOperand self state operand).bind
      (fun value => some (sourceRegisterPut state target (TransferScalarPowInvariant01.sourceRepeatedSquare count value))) = some updated at returned
    cases read : sourceOperand self state operand with
    | none => rw [read] at returned; cases returned
    | some value =>
      rw [read] at returned
      have same := Option.some.inj returned
      subst updated
      obtain ⟨exponent, exponentRead, valueEquation⟩ :=
        successful_corresponding_source_operand_derives_exact_exponent_read self state exponents operand value correspond read
      refine ⟨fun index => if index = target then some (exponent * 2 ^ count) else exponents index, ?_, ?_⟩
      · change (sourceExponentOperand exponents operand).bind _ = _
        rw [exponentRead] <;> rfl
      · apply matching_register_updates_preserve_field_exponent_correspondence self state exponents target _ _ correspond
        rw [symbolic_repeated_source_optimized_square_has_exact_mathematical_field_power, valueEquation,
          ← Nat.pow_mod, ← Nat.pow_mul]
  | multiply target left right =>
    change (sourceOperand self state left).bind (fun l => (sourceOperand self state right).bind
      (fun r => some (sourceRegisterPut state target (TransferScalarPowInvariant01.sourceCanonicalMul l r)))) = some updated at returned
    cases leftRead : sourceOperand self state left with
    | none => rw [leftRead] at returned; cases returned
    | some l =>
      rw [leftRead] at returned
      change (sourceOperand self state right).bind _ = some updated at returned
      cases rightRead : sourceOperand self state right with
      | none => rw [rightRead] at returned; cases returned
      | some r =>
        rw [rightRead] at returned
        have same := Option.some.inj returned
        subst updated
        obtain ⟨leftExponent, leftExponentRead, leftEquation⟩ :=
          successful_corresponding_source_operand_derives_exact_exponent_read self state exponents left l correspond leftRead
        obtain ⟨rightExponent, rightExponentRead, rightEquation⟩ :=
          successful_corresponding_source_operand_derives_exact_exponent_read self state exponents right r correspond rightRead
        refine ⟨fun index => if index = target then some (leftExponent + rightExponent) else exponents index, ?_, ?_⟩
        · change (sourceExponentOperand exponents left).bind (fun l => (sourceExponentOperand exponents right).bind _) = _
          rw [leftExponentRead]
          change (sourceExponentOperand exponents right).bind _ = _
          rw [rightExponentRead] <;> rfl
        · apply matching_register_updates_preserve_field_exponent_correspondence self state exponents target _ _ correspond
          rw [actual_modeled_canonical_multiply_has_exact_mathematical_field_value, leftEquation, rightEquation,
            Nat.mod_mul_mod, ← Nat.pow_add]

theorem successful_symbolic_source_walk_derives_matching_exponent_walk
    (self : CanonicalScalar) (instructions : List InvertInstruction) (state result : RegisterState)
    (exponents : Nat → Option Nat) (correspond : registersCorrespond self state exponents)
    (returned : sourceWalk self instructions state = some result) :
    ∃ resultExponents, sourceExponentWalk exponents instructions = some resultExponents ∧
      registersCorrespond self result resultExponents := by
  induction instructions generalizing state exponents with
  | nil =>
    have same := Option.some.inj returned
    subst result
    exact ⟨exponents, rfl, correspond⟩
  | cons instruction rest ih =>
    change (sourceApply self state instruction).bind (fun updated => sourceWalk self rest updated) = some result at returned
    cases applied : sourceApply self state instruction with
    | none => rw [applied] at returned; cases returned
    | some updated =>
      rw [applied] at returned
      obtain ⟨nextExponents, exponentApplied, nextCorrespond⟩ :=
        successful_source_instruction_derives_matching_exponent_instruction self state updated exponents instruction correspond applied
      obtain ⟨resultExponents, walked, resultCorrespond⟩ := ih updated nextExponents nextCorrespond returned
      refine ⟨resultExponents, ?_, resultCorrespond⟩
      change (sourceExponentApply exponents instruction).bind (fun updated => sourceExponentWalk updated rest) = some resultExponents
      rw [exponentApplied]
      exact walked

theorem exact_source_invert_payload_has_modulus_minus_two_field_power
    (self value : CanonicalScalar) (returned : sourceInvertPayload self = some value) :
    montgomeryValue value.words = montgomeryValue self.words ^ (nullifierModulus - 2) % nullifierModulus := by
  change (sourceWalk self sourceInvertInstructions (fun _ => none)).bind (fun registers => registers 0) = some value at returned
  cases walked : sourceWalk self sourceInvertInstructions (fun _ => none) with
  | none => rw [walked] at returned; cases returned
  | some registers =>
    rw [walked] at returned
    have initial : registersCorrespond self (fun _ => none) (fun _ => none) := by intro index; rfl
    obtain ⟨exponents, exponentWalk, correspond⟩ :=
      successful_symbolic_source_walk_derives_matching_exponent_walk self sourceInvertInstructions
        (fun _ => none) registers (fun _ => none) initial walked
    have certificate := source_invert_natural_exponent_instance_is_modulus_minus_two
    change (sourceExponentWalk (fun _ => none) sourceInvertInstructions).bind (fun registers => registers 0) = some (nullifierModulus - 2) at certificate
    rw [exponentWalk] at certificate
    have mapped := correspond 0
    change registers 0 = some value at returned
    change exponents 0 = some (nullifierModulus - 2) at certificate
    rw [returned, certificate] at mapped
    exact Option.some.inj mapped

set_option pp.all true in
#check @registersCorrespond
#print axioms registersCorrespond
set_option pp.all true in
#check @corresponding_registers_derive_corresponding_operand_values
#print axioms corresponding_registers_derive_corresponding_operand_values
set_option pp.all true in
#check @successful_corresponding_source_operand_derives_exact_exponent_read
#print axioms successful_corresponding_source_operand_derives_exact_exponent_read
set_option pp.all true in
#check @matching_register_updates_preserve_field_exponent_correspondence
#print axioms matching_register_updates_preserve_field_exponent_correspondence
set_option pp.all true in
#check @successful_source_instruction_derives_matching_exponent_instruction
#print axioms successful_source_instruction_derives_matching_exponent_instruction
set_option pp.all true in
#check @successful_symbolic_source_walk_derives_matching_exponent_walk
#print axioms successful_symbolic_source_walk_derives_matching_exponent_walk
set_option pp.all true in
#check @exact_source_invert_payload_has_modulus_minus_two_field_power
#print axioms exact_source_invert_payload_has_modulus_minus_two_field_power
end ShielddSecurity.TransferScalarInvertField01
