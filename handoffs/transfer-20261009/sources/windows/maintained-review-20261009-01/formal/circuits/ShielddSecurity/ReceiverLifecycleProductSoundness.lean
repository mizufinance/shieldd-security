import ShielddSecurity.ReceiverLifecycleProductCompletion

set_option maxHeartbeats 200000

namespace ShielddSecurity.ReceiverLifecycleProductSoundness

variable {F : Type} [Field F]

/-- Arbitrary satisfying values of the original product and zero assertion
force the enabled status product to vanish. No constructed assignment is used. -/
theorem materialized_sound (rho : Nat → F) (left right : Linear) (output auxiliary : Nat)
    (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho (ReceiverLifecycleProductCompletion.materializedRows left right output auxiliary)) :
    eval rho left * eval rho right = 0 := by
  have minusRow := satisfied ⟨Compiler.subtract left right,[(auxiliary,1)]⟩
    (List.mem_append_left _ (by simp [ScalarCompletion.productRows]))
  have minus : Square (eval rho left - eval rho right) (rho auxiliary) := by
    simpa only [Compiler.eval_subtract,eval,Int.cast_one,one_mul,add_zero] using minusRow
  have plusRow := satisfied ⟨left ++ right,[(auxiliary,1)] ++ scaleLinear 4 [(output,1)]⟩
    (List.mem_append_left _ (by simp [ScalarCompletion.productRows]))
  have plus : Square (eval rho left + eval rho right) (rho auxiliary + 4 * rho output) := by
    simpa only [eval_append,eval_scale,eval,Int.cast_ofNat,Int.cast_one,one_mul,add_zero] using plusRow
  have asserted := satisfied ⟨[(output,1)],[]⟩
    (List.mem_append_right _ (by simp))
  have zero : rho output = 0 := square_zero _ (by
    simpa only [eval,Int.cast_one,one_mul,add_zero] using asserted)
  exact (product_encoding (eval rho left) (eval rho right) (rho auxiliary) (rho output) four minus plus).trans zero

theorem enabled_bit (rho : Nat → F) (left right : Linear) (output auxiliary : Nat)
    (flag bit expected : Bool) (four : (4 : F) ≠ 0)
    (leftValue : eval rho left = if flag then 1 else 0)
    (rightValue : eval rho right = (if bit then 1 else 0) - (if expected then 1 else 0))
    (satisfied : Satisfies rho (ReceiverLifecycleProductCompletion.materializedRows left right output auxiliary))
    (enabled : flag = true) : bit = expected := by
  have product := materialized_sound rho left right output auxiliary four satisfied
  rw [leftValue,rightValue,enabled] at product
  simp only [if_true,one_mul] at product
  have same := sub_eq_zero.mp product
  cases bit <;> cases expected <;> simp_all

set_option pp.all true in
#check @materialized_sound
#print axioms materialized_sound
set_option pp.all true in
#check @enabled_bit
#print axioms enabled_bit

end ShielddSecurity.ReceiverLifecycleProductSoundness
