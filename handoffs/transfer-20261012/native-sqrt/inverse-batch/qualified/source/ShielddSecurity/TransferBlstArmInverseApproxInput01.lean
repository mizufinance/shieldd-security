import ShielddSecurity.TransferBlstArmInverseApproxBits01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseApproxInput01
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarSerializationRange01 (radix64)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
attribute [local irreducible] packWords

/-! Exact full limb input decomposition around the original low31 replacement.
Symbolic list tail, explicit radix split and casts avoid broad normalization.
High-window selection, batch progress, word multiplication and native ISA
remain separate. No desired factor row or final inverse premise is used. -/

theorem original_full_limb_input_has_the_exact_low31_radix_expansion
    (low : UInt64) (rest : List UInt64) :
    packWords (low::rest)=low.toNat%2147483648+
      2147483648*(low.toNat/2147483648+8589934592*packWords rest) := by
  have split := Nat.mod_add_div low.toNat 2147483648
  have radix : radix64=18446744073709551616 := by decide +kernel
  calc
    _ = low.toNat+18446744073709551616*packWords rest := by rw [packWords,radix]
    _ = (low.toNat%2147483648+2147483648*(low.toNat/2147483648))+
        18446744073709551616*packWords rest := by rw [split]
    _ = _ := by ring

theorem original_full_limb_input_signed_cast_has_the_exact_radix_expansion
    (low : UInt64) (rest : List UInt64) :
    (packWords (low::rest):Int)=((low.toNat%2147483648:Nat):Int)+
      2147483648*(((low.toNat/2147483648:Nat):Int)+8589934592*(packWords rest:Int)) := by
  have cast := congrArg (fun value : Nat => (value:Int))
    (original_full_limb_input_has_the_exact_low31_radix_expansion low rest)
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using cast

theorem original_low31_replacement_signed_cast_has_the_exact_radix_expansion
    (high low : UInt64) :
    (sourceApproxLow31 high low:Int)=((high.toNat/2147483648:Nat):Int)*2147483648+
      ((low.toNat%2147483648:Nat):Int) := by
  simp only [sourceApproxLow31,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]

theorem original_full_input_and_low31_approximation_have_an_exact_signed_radix_difference
    (high low : UInt64) (rest : List UInt64) :
    ∃ difference : Int, (packWords (low::rest):Int)=
      (sourceApproxLow31 high low:Int)+2147483648*difference := by
  refine ⟨((low.toNat/2147483648:Nat):Int)+8589934592*(packWords rest:Int)-
    ((high.toNat/2147483648:Nat):Int),?_⟩
  rw [original_full_limb_input_signed_cast_has_the_exact_radix_expansion,
    original_low31_replacement_signed_cast_has_the_exact_radix_expansion]
  ring

set_option pp.all true in
#check @original_full_limb_input_has_the_exact_low31_radix_expansion
#print axioms original_full_limb_input_has_the_exact_low31_radix_expansion
set_option pp.all true in
#check @original_full_limb_input_signed_cast_has_the_exact_radix_expansion
#print axioms original_full_limb_input_signed_cast_has_the_exact_radix_expansion
set_option pp.all true in
#check @original_low31_replacement_signed_cast_has_the_exact_radix_expansion
#print axioms original_low31_replacement_signed_cast_has_the_exact_radix_expansion
set_option pp.all true in
#check @original_full_input_and_low31_approximation_have_an_exact_signed_radix_difference
#print axioms original_full_input_and_low31_approximation_have_an_exact_signed_radix_difference
end ShielddSecurity.TransferBlstArmInverseApproxInput01
