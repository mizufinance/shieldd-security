import ShielddSecurity.TransferBlstArmInverseApproxParity01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseAbsOdd01

/-! Narrow signed integer absolute-value oddness; no word or native execution claim. -/

theorem odd_signed_integer_absolute_value_retains_oddness (value : Int) (odd : value%2=1) :
    value.natAbs%2=1 := by
  have bound := Nat.mod_lt value.natAbs (by decide : 0<2)
  have identity := Int.natAbs_emod value (by decide : (2:Int)≠0)
  rw [odd] at identity
  change (1:Nat)=(if 0≤value ∨ (2:Int) ∣ value then value.natAbs%2 else 2-value.natAbs%2) at identity
  split_ifs at identity <;> omega

set_option pp.all true in
#check @odd_signed_integer_absolute_value_retains_oddness
#print axioms odd_signed_integer_absolute_value_retains_oddness
end ShielddSecurity.TransferBlstArmInverseAbsOdd01
