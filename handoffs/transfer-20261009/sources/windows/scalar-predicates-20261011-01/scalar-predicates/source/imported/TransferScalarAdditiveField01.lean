import ShielddSecurity.TransferScalarCtOption01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarAdditiveField01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferScalarMontgomeryValue01 (radixInverse montgomeryValue)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarProgramInvariant01 (certifyResult)
/-! Mathematical meaning of the already qualified actual source ADC/SBB/
masked-addback/nonzero-mask outputs. Small symbolic modular lemmas remove
the Montgomery factor without walking wide constraints or assuming the
desired mathematical output. Canonical inputs are the typed model domain;
all output range/width premises come from qualified source word contracts.
Rust compiler/ABI/private constructor/native caller/full Transfer coupling
remain separate; no new executed runtime or negative control is claimed. -/

theorem canonical_additive_residue_equation_determines_exact_modular_difference
    (left right output : Nat)
    (rightRange : right < nullifierModulus) (outputRange : output < nullifierModulus)
    (relation : (output + right) % nullifierModulus = left) :
    output = (left + nullifierModulus - right) % nullifierModulus := by
  by_cases noWrap : output + right < nullifierModulus
  · rw [Nat.mod_eq_of_lt noWrap] at relation
    have identity : left + nullifierModulus - right = output + nullifierModulus := by omega
    rw [identity, Nat.add_mod_right, Nat.mod_eq_of_lt outputRange]
  · have smaller : output + right - nullifierModulus < nullifierModulus := by omega
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt smaller] at relation
    have identity : left + nullifierModulus - right = output := by omega
    rw [identity, Nat.mod_eq_of_lt outputRange]

theorem actual_raw_montgomery_subtraction_contract_derives_mathematical_field_difference
    (left right output : Nat) (leftRange : left < nullifierModulus)
    (rightRange : right < nullifierModulus)
    (rawContract : output = (left + nullifierModulus - right) % nullifierModulus) :
    (radixInverse * output) % nullifierModulus =
      ((radixInverse * left) % nullifierModulus + nullifierModulus -
        (radixInverse * right) % nullifierModulus) % nullifierModulus := by
  have rawRelation : (output + right) % nullifierModulus = left := by
    rw [rawContract, Nat.mod_add_mod, Nat.sub_add_cancel (by omega),
      Nat.add_mod_right, Nat.mod_eq_of_lt leftRange]
  have scaled := congrArg (fun value : Nat => radixInverse * value % nullifierModulus) rawRelation
  dsimp only at scaled
  rw [Nat.mul_mod_mod, Nat.mul_add, Nat.add_mod] at scaled
  exact canonical_additive_residue_equation_determines_exact_modular_difference _ _ _
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) scaled

def sourceCanonicalAdd (left right : CanonicalScalar) : CanonicalScalar :=
  let contract := TransferScalarCanonicalAdd01.source_four_adc_and_modulus_sub_preserve_canonical_modular_sum left right
  certifyResult (TransferScalarCanonicalAdd01.sourceAddWords left.words right.words) contract.1 contract.2.1

theorem actual_source_canonical_add_has_exact_mathematical_field_sum (left right : CanonicalScalar) :
    montgomeryValue (sourceCanonicalAdd left right).words =
      (montgomeryValue left.words + montgomeryValue right.words) % nullifierModulus := by
  have contract := TransferScalarCanonicalAdd01.source_four_adc_and_modulus_sub_preserve_canonical_modular_sum left right
  change (radixInverse * packWords (TransferScalarCanonicalAdd01.sourceAddWords left.words right.words).toArray.toList) % nullifierModulus =
    ((radixInverse * packWords left.words.toList) % nullifierModulus +
      (radixInverse * packWords right.words.toList) % nullifierModulus) % nullifierModulus
  rw [List.toList_toArray, contract.2.2, Nat.mul_mod_mod, Nat.mul_add, Nat.add_mod]

def sourceCanonicalSub (left right : CanonicalScalar) : CanonicalScalar :=
  let width := TransferScalarCanonicalSub01.source_four_sbb_and_masked_adc_retain_four_output_limbs left.words right.words
  let contract := TransferScalarCanonicalSub01.canonical_operands_source_subtraction_has_exact_canonical_modular_value left right
  certifyResult (TransferScalarCanonicalSub01.sourceSubWords left.words right.words) width contract.1

theorem actual_source_canonical_sub_has_exact_mathematical_field_difference (left right : CanonicalScalar) :
    montgomeryValue (sourceCanonicalSub left right).words =
      (montgomeryValue left.words + nullifierModulus - montgomeryValue right.words) % nullifierModulus := by
  have contract := TransferScalarCanonicalSub01.canonical_operands_source_subtraction_has_exact_canonical_modular_value left right
  change (radixInverse * packWords (TransferScalarCanonicalSub01.sourceSubWords left.words right.words).toArray.toList) % nullifierModulus =
    ((radixInverse * packWords left.words.toList) % nullifierModulus + nullifierModulus -
      (radixInverse * packWords right.words.toList) % nullifierModulus) % nullifierModulus
  rw [List.toList_toArray]
  exact actual_raw_montgomery_subtraction_contract_derives_mathematical_field_difference _ _ _
    left.canonical right.canonical contract.2

def sourceCanonicalNeg (scalar : CanonicalScalar) : CanonicalScalar :=
  let contract := TransferScalarCanonicalNeg01.source_four_sbb_and_nonzero_mask_derive_canonical_negation scalar
  certifyResult (TransferScalarCanonicalNeg01.sourceNegWords scalar.words) contract.1 contract.2.1

theorem actual_source_canonical_negation_has_exact_mathematical_field_value (scalar : CanonicalScalar) :
    montgomeryValue (sourceCanonicalNeg scalar).words =
      (nullifierModulus - montgomeryValue scalar.words) % nullifierModulus := by
  have contract := TransferScalarCanonicalNeg01.source_four_sbb_and_nonzero_mask_derive_canonical_negation scalar
  have raw : packWords (TransferScalarCanonicalNeg01.sourceNegWords scalar.words) =
      (0 + nullifierModulus - packWords scalar.words.toList) % nullifierModulus := by
    rw [Nat.zero_add]; exact contract.2.2
  have meaning := actual_raw_montgomery_subtraction_contract_derives_mathematical_field_difference
    0 (packWords scalar.words.toList) (packWords (TransferScalarCanonicalNeg01.sourceNegWords scalar.words))
    (by decide) scalar.canonical raw
  change (radixInverse * packWords (TransferScalarCanonicalNeg01.sourceNegWords scalar.words).toArray.toList) % nullifierModulus = _
  rw [List.toList_toArray]
  simpa only [Nat.mul_zero, Nat.zero_mod, Nat.zero_add] using meaning

set_option pp.all true in
#check @canonical_additive_residue_equation_determines_exact_modular_difference
#print axioms canonical_additive_residue_equation_determines_exact_modular_difference
set_option pp.all true in
#check @actual_raw_montgomery_subtraction_contract_derives_mathematical_field_difference
#print axioms actual_raw_montgomery_subtraction_contract_derives_mathematical_field_difference
set_option pp.all true in
#check @sourceCanonicalAdd
#print axioms sourceCanonicalAdd
set_option pp.all true in
#check @actual_source_canonical_add_has_exact_mathematical_field_sum
#print axioms actual_source_canonical_add_has_exact_mathematical_field_sum
set_option pp.all true in
#check @sourceCanonicalSub
#print axioms sourceCanonicalSub
set_option pp.all true in
#check @actual_source_canonical_sub_has_exact_mathematical_field_difference
#print axioms actual_source_canonical_sub_has_exact_mathematical_field_difference
set_option pp.all true in
#check @sourceCanonicalNeg
#print axioms sourceCanonicalNeg
set_option pp.all true in
#check @actual_source_canonical_negation_has_exact_mathematical_field_value
#print axioms actual_source_canonical_negation_has_exact_mathematical_field_value
end ShielddSecurity.TransferScalarAdditiveField01
