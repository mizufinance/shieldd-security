import ShielddSecurity.UserWordSeed342
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.UserLifecycleBits344

theorem encoded_bit (width n index : Nat) (inside : index < width) :
    (encodeBits width n)[index]?.getD false = decide (n / 2^index % 2 = 1) := by
  induction width generalizing n index with
  | zero => omega
  | succ width ih =>
    cases index with
    | zero => simp only [encodeBits,List.getElem?_cons_zero,Option.getD_some,Nat.pow_zero,Nat.div_one]
    | succ index =>
      simp only [encodeBits,List.getElem?_cons_succ]
      rw [ih (n/2) index (by omega),Nat.div_div_eq_div_mul,Nat.pow_succ']

theorem status_bit (n index : Nat) (active : n%8=1) (inside : index<3) :
    (encodeBits 131 n)[index]?.getD false = decide (index=0) := by
  rw [encoded_bit 131 n index (by omega)]
  have cases : index=0 ∨ index=1 ∨ index=2 := by omega
  rcases cases with rfl|rfl|rfl
  · simp only [Nat.pow_zero,Nat.div_one]
    have low : n%2=1 := by omega
    rw [low]
    rfl
  · have low : n/2%2=0 := by omega
    simp only [Nat.pow_one,low]
    rfl
  · have low : n/4%2=0 := by omega
    change decide (n/4%2=1)=false
    rw [low]
    rfl

theorem high_bit (n index : Nat) (highZero : n/2^67=0) (later : 67 ≤ index)
    (inside : index<131) : (encodeBits 131 n)[index]?.getD false = false := by
  rw [encoded_bit 131 n index inside]
  have decomposition := Nat.mod_add_div n (2^67)
  rw [highZero,Nat.mul_zero,Nat.add_zero] at decomposition
  have bound : n < 2^67 := decomposition ▸ Nat.mod_lt n (by decide)
  have power : 2^67 ≤ 2^index := Nat.pow_le_pow_right (by decide) later
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le bound power)]
  rfl
end ShielddSecurity.UserLifecycleBits344

set_option pp.all true in
#check @ShielddSecurity.UserLifecycleBits344.encoded_bit
#print axioms ShielddSecurity.UserLifecycleBits344.encoded_bit

set_option pp.all true in
#check @ShielddSecurity.UserLifecycleBits344.status_bit
#print axioms ShielddSecurity.UserLifecycleBits344.status_bit

set_option pp.all true in
#check @ShielddSecurity.UserLifecycleBits344.high_bit
#print axioms ShielddSecurity.UserLifecycleBits344.high_bit
