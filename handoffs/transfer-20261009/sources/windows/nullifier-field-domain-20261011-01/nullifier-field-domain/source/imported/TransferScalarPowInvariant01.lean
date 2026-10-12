import ShielddSecurity.TransferScalarSquareProduct01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarPowInvariant01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarProgramInvariant01 (certifyResult)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarLittleEndianBytes01 (decodeLE serializerBytes)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Source-shaped repeated square and conditional multiply operations use
the proved canonical word outputs. Pow's reverse word/bit loops compute the
multiply on every bit; pow_vartime computes it only on the selected branch.
Their modeled returned fields agree and derive the private invariant from
the source ONE constant and operation results. Native Choice/conditional
assignment, compiler/caller coupling and exponent semantics are separate. -/

def sourceZero : CanonicalScalar :=
  ⟨#v[0, 0, 0, 0], by decide⟩

def sourceOne : CanonicalScalar :=
  ⟨#v[0x00000001fffffffe, 0x5884b7fa00034802, 0x998c4fefecbc4ff5, 0x1824b159acc5056f], by decide⟩

def sourceCanonicalMul (left right : CanonicalScalar) : CanonicalScalar :=
  let contract := TransferScalarWideReduction01.canonical_right_operand_source_multiplication_has_derived_montgomery_contract
    left.words right.words right.canonical
  certifyResult (TransferScalarWideReduction01.sourceMulMontgomery left.words right.words) contract.1 contract.2.1

def sourceCanonicalSquare (value : CanonicalScalar) : CanonicalScalar :=
  let contract := TransferScalarSquareProduct01.canonical_operand_source_square_derives_canonical_montgomery_contract
    value.words value.canonical
  certifyResult (TransferScalarSquareProduct01.sourceSquareMontgomery value.words) contract.1 contract.2.1

def sourcePowBit (word : UInt64) (index : Nat) : Bool :=
  ((word >>> UInt64.ofNat index) &&& 1) == 1

def sourceConstantTimeStep (self result : CanonicalScalar) (bit : Bool) : CanonicalScalar :=
  let squared := sourceCanonicalSquare result
  let multiplied := sourceCanonicalMul squared self
  if bit then multiplied else squared

def sourceVariableTimeStep (self result : CanonicalScalar) (bit : Bool) : CanonicalScalar :=
  let squared := sourceCanonicalSquare result
  if bit then sourceCanonicalMul squared self else squared

def sourcePowLoop (step : CanonicalScalar → Bool → CanonicalScalar)
    (exponent : Vector UInt64 4) : CanonicalScalar :=
  exponent.toList.reverse.foldl (fun result word =>
    (List.range 64).reverse.foldl (fun current index => step current (sourcePowBit word index)) result) sourceOne

def sourcePow (self : CanonicalScalar) (exponent : Vector UInt64 4) : CanonicalScalar :=
  sourcePowLoop (sourceConstantTimeStep self) exponent

def sourcePowVartime (self : CanonicalScalar) (exponent : Vector UInt64 4) : CanonicalScalar :=
  sourcePowLoop (sourceVariableTimeStep self) exponent

def sourceRepeatedSquare : Nat → CanonicalScalar → CanonicalScalar
  | 0, value => value
  | count + 1, value => sourceRepeatedSquare count (sourceCanonicalSquare value)

theorem source_zero_and_one_constants_have_exact_canonical_montgomery_keys :
    montgomeryValue sourceZero.words = 0 ∧ montgomeryValue sourceOne.words = 1 := by decide

theorem source_constant_and_variable_bit_steps_return_identical_fields
    (self result : CanonicalScalar) (bit : Bool) :
    sourceConstantTimeStep self result bit = sourceVariableTimeStep self result bit := by rfl

theorem source_constant_and_variable_pow_loops_return_identical_fields
    (self : CanonicalScalar) (exponent : Vector UInt64 4) :
    sourcePow self exponent = sourcePowVartime self exponent := by rfl

theorem source_pow_and_repeated_square_derive_canonical_fields_and_exact_serialization
    (self : CanonicalScalar) (exponent : Vector UInt64 4) (count : Nat) :
    packWords (sourcePow self exponent).words.toList < nullifierModulus ∧
      packWords (sourceRepeatedSquare count self).words.toList < nullifierModulus ∧
      (serializerBytes (sourcePow self exponent).words.toList).length = 32 ∧
      decodeLE (serializerBytes (sourcePow self exponent).words.toList) < nullifierModulus ∧
      decodeLE (serializerBytes (sourcePow self exponent).words.toList) = montgomeryValue (sourcePow self exponent).words := by
  exact ⟨(sourcePow self exponent).canonical, (sourceRepeatedSquare count self).canonical,
    TransferCheckedWordAcceptedInput01.every_original_typed_field_has_exact_32_byte_canonical_serialized_key (sourcePow self exponent)⟩

set_option pp.all true in
#check @sourceZero
#print axioms sourceZero
set_option pp.all true in
#check @sourceOne
#print axioms sourceOne
set_option pp.all true in
#check @sourceCanonicalMul
#print axioms sourceCanonicalMul
set_option pp.all true in
#check @sourceCanonicalSquare
#print axioms sourceCanonicalSquare
set_option pp.all true in
#check @sourcePowBit
#print axioms sourcePowBit
set_option pp.all true in
#check @sourceConstantTimeStep
#print axioms sourceConstantTimeStep
set_option pp.all true in
#check @sourceVariableTimeStep
#print axioms sourceVariableTimeStep
set_option pp.all true in
#check @sourcePowLoop
#print axioms sourcePowLoop
set_option pp.all true in
#check @sourcePow
#print axioms sourcePow
set_option pp.all true in
#check @sourcePowVartime
#print axioms sourcePowVartime
set_option pp.all true in
#check @sourceRepeatedSquare
#print axioms sourceRepeatedSquare
set_option pp.all true in
#check @source_zero_and_one_constants_have_exact_canonical_montgomery_keys
#print axioms source_zero_and_one_constants_have_exact_canonical_montgomery_keys
set_option pp.all true in
#check @source_constant_and_variable_bit_steps_return_identical_fields
#print axioms source_constant_and_variable_bit_steps_return_identical_fields
set_option pp.all true in
#check @source_constant_and_variable_pow_loops_return_identical_fields
#print axioms source_constant_and_variable_pow_loops_return_identical_fields
set_option pp.all true in
#check @source_pow_and_repeated_square_derive_canonical_fields_and_exact_serialization
#print axioms source_pow_and_repeated_square_derive_canonical_fields_and_exact_serialization
end ShielddSecurity.TransferScalarPowInvariant01
