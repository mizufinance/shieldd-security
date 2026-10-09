import ShielddSecurity.ScalarBits
import Init.Data.BitVec.Lemmas

set_option maxHeartbeats 300000

namespace ShielddSecurity.RoutingNativeWord

/-- Integer model of the owned u64 shift/subtract followed by the u32 cast.
The caller must establish precision ≤ 32 before executing that expression. -/
def mask (precision : Nat) : BitVec 32 := BitVec.ofNat 32 (2 ^ precision - 1)

/-- Exact owned u32 AND/OR/complement expression, including its meaningful branch. -/
def word (meaningful : Bool) (precision : Nat) (route random : BitVec 32) : BitVec 32 :=
  if meaningful then (route &&& mask precision) ||| (random &&& ~~~(mask precision))
  else random

theorem mask_bit (precision : Nat) (bit : Fin 32) :
    (mask precision).getLsbD bit.val = decide (bit.val < precision) := by
  simp only [mask, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  simp only [bit.isLt, decide_true, Bool.true_and]

theorem word_bit (meaningful : Bool) (precision : Nat) (route random : BitVec 32)
    (bit : Fin 32) :
    (word meaningful precision route random).getLsbD bit.val =
      if meaningful && decide (bit.val < precision) then route.getLsbD bit.val
      else random.getLsbD bit.val := by
  cases meaningful with
  | false => simp only [word, Bool.false_eq_true, if_false, Bool.false_and]
  | true =>
    simp only [word, if_true, BitVec.getLsbD_or,
      BitVec.getLsbD_and, BitVec.getLsbD_not, mask_bit, bit.isLt, decide_true,
      Bool.true_and]
    by_cases active : bit.val < precision <;> simp only [active, decide_true,
      decide_false, Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false,
      Bool.or_false, Bool.false_or, Bool.false_eq_true, if_true, if_false]

theorem word_semantics (meaningful : Bool) (precision : Nat) (route random : BitVec 32) :
    (word meaningful precision route random).toNat < 2 ^ 32 ∧
      ∀ bit : Fin 32,
        decide ((word meaningful precision route random).toNat / 2 ^ bit.val % 2 = 1) =
          if meaningful && decide (bit.val < precision)
          then decide (route.toNat / 2 ^ bit.val % 2 = 1)
          else decide (random.toNat / 2 ^ bit.val % 2 = 1) := by
  constructor
  · exact (word meaningful precision route random).isLt
  · intro bit
    simpa only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq] using
      word_bit meaningful precision route random bit

set_option pp.all true in
#check @mask_bit
#print axioms mask_bit
set_option pp.all true in
#check @word_bit
#print axioms word_bit
set_option pp.all true in
#check @word_semantics
#print axioms word_semantics

end ShielddSecurity.RoutingNativeWord
