import ShielddSecurity.TransferScalarInvertMachine01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarInvertChain01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarInvertMachine01
open TransferScalarPowInvariant01 (sourceZero)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarLittleEndianBytes01 (serializerBytes decodeLE)
open TransferScalarMontgomeryValue01 (montgomeryValue)
/-! Generated from the exact authenticated cached invert body. Each source
statement is retained in the generator context in original order. This
instance proves initialized reads, successful canonical payload, exact zero
refusal and a separate natural-exponent p-2 certificate. Field exponent/
inverse semantics and native Choice/compiler/caller coupling remain open. -/
def sourceOperandDecider (defined : List Nat) (operand : InvertOperand) :
    Decidable (operandInitialized defined operand) :=
  match operand with
  | .input => .isTrue True.intro
  | .register index => inferInstanceAs (Decidable (index ∈ defined))

def sourceInstructionDecider (defined : List Nat) (instruction : InvertInstruction) :
    Decidable (instructionReadsInitialized defined instruction) :=
  match instruction with
  | .square _ source _ => sourceOperandDecider defined source
  | .multiply _ left right =>
    match sourceOperandDecider defined left, sourceOperandDecider defined right with
    | .isTrue l, .isTrue r => .isTrue ⟨l, r⟩
    | .isFalse l, _ => .isFalse (fun h => l h.1)
    | _, .isFalse r => .isFalse (fun h => r h.2)

def sourceChainDecider (defined : List Nat) : (instructions : List InvertInstruction) →
    Decidable (sourceWellFormed defined instructions)
  | [] => .isTrue True.intro
  | instruction :: rest =>
    match sourceInstructionDecider defined instruction,
        sourceChainDecider (instructionTarget instruction :: defined) rest with
    | .isTrue first, .isTrue tail => .isTrue ⟨first, tail⟩
    | .isFalse first, _ => .isFalse (fun h => first h.1)
    | _, .isFalse tail => .isFalse (fun h => tail h.2)

def sourceInvertInstructions : List InvertInstruction := [
  .square 0 .input 1,
  .multiply 1 (.register 0) .input,
  .square 16 (.register 0) 1,
  .square 6 (.register 16) 1,
  .multiply 5 (.register 6) (.register 0),
  .multiply 0 (.register 6) (.register 16),
  .multiply 12 (.register 5) (.register 16),
  .square 2 (.register 6) 1,
  .multiply 7 (.register 5) (.register 6),
  .multiply 15 (.register 0) (.register 5),
  .square 17 (.register 12) 1,
  .multiply 1 (.register 1) (.register 17),
  .multiply 3 (.register 7) (.register 2),
  .multiply 8 (.register 1) (.register 17),
  .multiply 4 (.register 8) (.register 2),
  .multiply 9 (.register 8) (.register 7),
  .multiply 7 (.register 4) (.register 5),
  .multiply 11 (.register 4) (.register 17),
  .multiply 5 (.register 9) (.register 17),
  .multiply 14 (.register 7) (.register 15),
  .multiply 13 (.register 11) (.register 12),
  .multiply 12 (.register 11) (.register 17),
  .multiply 15 (.register 15) (.register 12),
  .multiply 16 (.register 16) (.register 15),
  .multiply 3 (.register 3) (.register 16),
  .multiply 17 (.register 17) (.register 3),
  .multiply 0 (.register 0) (.register 17),
  .multiply 6 (.register 6) (.register 0),
  .multiply 2 (.register 2) (.register 6),
  .square 0 (.register 0) 8,
  .multiply 0 (.register 0) (.register 17),
  .square 0 (.register 0) 9,
  .multiply 0 (.register 0) (.register 16),
  .square 0 (.register 0) 9,
  .multiply 0 (.register 0) (.register 15),
  .square 0 (.register 0) 9,
  .multiply 0 (.register 0) (.register 15),
  .square 0 (.register 0) 7,
  .multiply 0 (.register 0) (.register 14),
  .square 0 (.register 0) 7,
  .multiply 0 (.register 0) (.register 13),
  .square 0 (.register 0) 10,
  .multiply 0 (.register 0) (.register 12),
  .square 0 (.register 0) 9,
  .multiply 0 (.register 0) (.register 11),
  .square 0 (.register 0) 8,
  .multiply 0 (.register 0) (.register 8),
  .square 0 (.register 0) 8,
  .multiply 0 (.register 0) .input,
  .square 0 (.register 0) 14,
  .multiply 0 (.register 0) (.register 9),
  .square 0 (.register 0) 10,
  .multiply 0 (.register 0) (.register 8),
  .square 0 (.register 0) 15,
  .multiply 0 (.register 0) (.register 7),
  .square 0 (.register 0) 10,
  .multiply 0 (.register 0) (.register 6),
  .square 0 (.register 0) 8,
  .multiply 0 (.register 0) (.register 5),
  .square 0 (.register 0) 16,
  .multiply 0 (.register 0) (.register 3),
  .square 0 (.register 0) 8,
  .multiply 0 (.register 0) (.register 2),
  .square 0 (.register 0) 7,
  .multiply 0 (.register 0) (.register 4),
  .square 0 (.register 0) 9,
  .multiply 0 (.register 0) (.register 2),
  .square 0 (.register 0) 8,
  .multiply 0 (.register 0) (.register 3),
  .square 0 (.register 0) 8,
  .multiply 0 (.register 0) (.register 2),
  .square 0 (.register 0) 8,
  .multiply 0 (.register 0) (.register 2),
  .square 0 (.register 0) 8,
  .multiply 0 (.register 0) (.register 2),
  .square 0 (.register 0) 8,
  .multiply 0 (.register 0) (.register 3),
  .square 0 (.register 0) 8,
  .multiply 0 (.register 0) (.register 2),
  .square 0 (.register 0) 8,
  .multiply 0 (.register 0) (.register 2),
  .square 0 (.register 0) 5,
  .multiply 0 (.register 0) (.register 1),
  .square 0 (.register 0) 5,
  .multiply 0 (.register 0) (.register 1)]

theorem source_invert_instruction_reads_are_well_formed :
    sourceWellFormed [] sourceInvertInstructions := by
  letI := sourceChainDecider [] sourceInvertInstructions
  decide

theorem source_invert_final_result_register_is_initialized :
    0 ∈ sourceAssigned [] sourceInvertInstructions := by decide

theorem source_invert_natural_exponent_instance_is_modulus_minus_two :
    (do
      let result ← sourceExponentWalk (fun _ => none) sourceInvertInstructions
      result 0) = some (TransferBoundedNativeCodec01.nullifierModulus - 2) := by decide

def sourceInvertPayload (self : CanonicalScalar) : Option CanonicalScalar := do
  let registers ← sourceWalk self sourceInvertInstructions (fun _ => none)
  registers 0

def sourceInvert (self : CanonicalScalar) : Option CanonicalScalar :=
  if self.words = sourceZero.words then none else sourceInvertPayload self

theorem exact_source_invert_chain_derives_successful_canonical_payload (self : CanonicalScalar) :
    ∃ scalar, sourceInvertPayload self = some scalar := by
  have initial : registerInitialized (fun _ => none) [] := by
    intro index inside
    cases inside
  obtain ⟨registers, walked, initialized⟩ :=
    well_formed_symbolic_inversion_walk_derives_successful_initialized_result
      self sourceInvertInstructions (fun _ => none) [] initial source_invert_instruction_reads_are_well_formed
  obtain ⟨scalar, returned⟩ := initialized 0 source_invert_final_result_register_is_initialized
  refine ⟨scalar, ?_⟩
  change (sourceWalk self sourceInvertInstructions (fun _ => none)).bind (fun registers => registers 0) = some scalar
  rw [walked]
  exact returned

theorem exact_source_invert_zero_refusal_is_derived (self : CanonicalScalar) :
    sourceInvert self = none ↔ self.words = sourceZero.words := by
  by_cases zero : self.words = sourceZero.words
  · constructor
    · intro _
      exact zero
    · intro _
      exact if_pos zero
  · obtain ⟨scalar, returned⟩ := exact_source_invert_chain_derives_successful_canonical_payload self
    constructor
    · intro refused
      change (if self.words = sourceZero.words then none else sourceInvertPayload self) = none at refused
      rw [if_neg zero, returned] at refused
      cases refused
    · intro same
      exact False.elim (zero same)

theorem exact_returned_source_invert_derives_canonical_fields_and_exact_serialization
    (self : CanonicalScalar) :
    match sourceInvert self with
    | none => True
    | some scalar => packWords scalar.words.toList < TransferBoundedNativeCodec01.nullifierModulus ∧
        (serializerBytes scalar.words.toList).length = 32 ∧
        decodeLE (serializerBytes scalar.words.toList) < TransferBoundedNativeCodec01.nullifierModulus ∧
        decodeLE (serializerBytes scalar.words.toList) = montgomeryValue scalar.words := by
  cases sourceInvert self with
  | none => trivial
  | some scalar => exact ⟨scalar.canonical,
      TransferCheckedWordAcceptedInput01.every_original_typed_field_has_exact_32_byte_canonical_serialized_key scalar⟩

set_option pp.all true in
#check @sourceOperandDecider
#print axioms sourceOperandDecider

set_option pp.all true in
#check @sourceInstructionDecider
#print axioms sourceInstructionDecider

set_option pp.all true in
#check @sourceChainDecider
#print axioms sourceChainDecider

set_option pp.all true in
#check @sourceInvertInstructions
#print axioms sourceInvertInstructions

set_option pp.all true in
#check @source_invert_instruction_reads_are_well_formed
#print axioms source_invert_instruction_reads_are_well_formed

set_option pp.all true in
#check @source_invert_final_result_register_is_initialized
#print axioms source_invert_final_result_register_is_initialized

set_option pp.all true in
#check @source_invert_natural_exponent_instance_is_modulus_minus_two
#print axioms source_invert_natural_exponent_instance_is_modulus_minus_two

set_option pp.all true in
#check @sourceInvertPayload
#print axioms sourceInvertPayload

set_option pp.all true in
#check @sourceInvert
#print axioms sourceInvert

set_option pp.all true in
#check @exact_source_invert_chain_derives_successful_canonical_payload
#print axioms exact_source_invert_chain_derives_successful_canonical_payload

set_option pp.all true in
#check @exact_source_invert_zero_refusal_is_derived
#print axioms exact_source_invert_zero_refusal_is_derived

set_option pp.all true in
#check @exact_returned_source_invert_derives_canonical_fields_and_exact_serialization
#print axioms exact_returned_source_invert_derives_canonical_fields_and_exact_serialization
end ShielddSecurity.TransferScalarInvertChain01
