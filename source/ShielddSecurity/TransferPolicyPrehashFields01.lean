import ShielddSecurity.TransferScalarPackWalk01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferPolicyPrehashFields01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferScalarPackWalk01 (sourcePackByteFields)
/-! Source policy_identifier prehash field vector: checked u64 length field
followed by ordered encoding::pack bytes. The explicit conversion domain
derives exact length meaning; returned field vectors bind every original
byte injectively. Option describes checked conversion/returned values only:
native expect panic, hash primitive/domain, iterator/Vec/compiler/ABI/caller
correspondence remain open. No hash collision-resistance/injectivity claim. -/

def sourcePolicyLengthField (bytes : List UInt8) : CanonicalScalar :=
  TransferScalarProgramInvariant01.sourceEval (.raw #v[UInt64.ofNat bytes.length, 0, 0, 0])

theorem checked_source_policy_length_field_has_the_exact_original_length
    (bytes : List UInt8) (bounded : bytes.length < UInt64.size) :
    montgomeryValue (sourcePolicyLengthField bytes).words = bytes.length := by
  have value := TransferScalarExtendedSemantics01.source_u64_constructor_has_exact_integer_field_semantics
    (UInt64.ofNat bytes.length)
  change some (montgomeryValue (sourcePolicyLengthField bytes).words) = some (UInt64.ofNat bytes.length).toNat at value
  have exactNat : (UInt64.ofNat bytes.length).toNat = bytes.length := by
    change bytes.length % UInt64.size = bytes.length
    exact Nat.mod_eq_of_lt bounded
  exact (Option.some.inj value).trans exactNat

def sourcePolicyIdentifierFields (bytes : List UInt8) : Option (List CanonicalScalar) :=
  if bytes.length < UInt64.size then some (sourcePolicyLengthField bytes :: sourcePackByteFields bytes) else none

theorem source_policy_prehash_fields_return_exactly_on_checked_length_domain (bytes : List UInt8) :
    (∃ fields, sourcePolicyIdentifierFields bytes = some fields) ↔ bytes.length < UInt64.size := by
  by_cases bounded : bytes.length < UInt64.size
  · constructor
    · intro _; exact bounded
    · intro _; exact ⟨_, by rw [sourcePolicyIdentifierFields, if_pos bounded]⟩
  · constructor
    · rintro ⟨fields, returned⟩
      rw [sourcePolicyIdentifierFields, if_neg bounded] at returned
      cases returned
    · intro yes; exact False.elim (bounded yes)

theorem every_returned_source_policy_prehash_vector_has_the_exact_length_prefix_and_ordered_pack
    (bytes : List UInt8) (fields : List CanonicalScalar) (returned : sourcePolicyIdentifierFields bytes = some fields) :
    fields = sourcePolicyLengthField bytes :: sourcePackByteFields bytes ∧
      montgomeryValue (sourcePolicyLengthField bytes).words = bytes.length := by
  have bounded := (source_policy_prehash_fields_return_exactly_on_checked_length_domain bytes).mp ⟨fields, returned⟩
  rw [sourcePolicyIdentifierFields, if_pos bounded] at returned
  exact ⟨(Option.some.inj returned).symm, checked_source_policy_length_field_has_the_exact_original_length bytes bounded⟩

theorem source_policy_identifier_prehash_field_vector_binds_exact_original_bytes_injectively
    (left right : List UInt8) (fields : List CanonicalScalar)
    (leftReturned : sourcePolicyIdentifierFields left = some fields)
    (rightReturned : sourcePolicyIdentifierFields right = some fields) : left = right := by
  have leftVector := every_returned_source_policy_prehash_vector_has_the_exact_length_prefix_and_ordered_pack left fields leftReturned
  have rightVector := every_returned_source_policy_prehash_vector_has_the_exact_length_prefix_and_ordered_pack right fields rightReturned
  have vectors := leftVector.1.symm.trans rightVector.1
  have heads := List.cons.inj vectors |>.1
  have tails := List.cons.inj vectors |>.2
  have lengths := congrArg (fun scalar : CanonicalScalar => montgomeryValue scalar.words) heads
  dsimp only at lengths
  rw [leftVector.2, rightVector.2] at lengths
  exact TransferScalarPackWalk01.complete_source_byte_packing_is_injective_when_exact_input_length_is_bound
    left right lengths (congrArg (List.map (fun scalar : CanonicalScalar => montgomeryValue scalar.words)) tails)

set_option pp.all true in
#check @sourcePolicyLengthField
#print axioms sourcePolicyLengthField
set_option pp.all true in
#check @checked_source_policy_length_field_has_the_exact_original_length
#print axioms checked_source_policy_length_field_has_the_exact_original_length
set_option pp.all true in
#check @sourcePolicyIdentifierFields
#print axioms sourcePolicyIdentifierFields
set_option pp.all true in
#check @source_policy_prehash_fields_return_exactly_on_checked_length_domain
#print axioms source_policy_prehash_fields_return_exactly_on_checked_length_domain
set_option pp.all true in
#check @every_returned_source_policy_prehash_vector_has_the_exact_length_prefix_and_ordered_pack
#print axioms every_returned_source_policy_prehash_vector_has_the_exact_length_prefix_and_ordered_pack
set_option pp.all true in
#check @source_policy_identifier_prehash_field_vector_binds_exact_original_bytes_injectively
#print axioms source_policy_identifier_prehash_field_vector_binds_exact_original_bytes_injectively
end ShielddSecurity.TransferPolicyPrehashFields01
