import ShielddSecurity.TransferBlstArmInverseWindowAlign01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWindowClz01
open TransferBlstArmInverseWindowAlign01

/-! Mac import-minimized replay variant of the desktop handwritten model of joint OR/CLZ and its zero-window fallback.
The CLZ count comes from the original selected high words, before the fallback
replaces them with the low words. Actual upstream limb selection and complete
input correspondence remain open. The fallback must later be handled as a
one-word case, rather than silently using a two-word prefix decomposition. -/

structure SourceCommonWindow where
  highA : UInt64
  highB : UInt64
  count : Nat

def sourceCommonWindow (highA highB lowA lowB : UInt64) : SourceCommonWindow :=
  let count := (highA ||| highB).toBitVec.clz.toNat
  if count = 64 then ⟨lowA, lowB, 0⟩ else ⟨highA, highB, count⟩

theorem original_common_clz_window_derives_both_high_bounds_and_a_bounded_count
    (highA highB lowA lowB : UInt64) :
    let w := sourceCommonWindow highA highB lowA lowB
    w.count < 64 ∧ w.highA.toNat < 2 ^ (64 - w.count) ∧
      w.highB.toNat < 2 ^ (64 - w.count) := by
  dsimp only [sourceCommonWindow]
  by_cases zero : (highA ||| highB).toBitVec.clz.toNat = 64
  · rw [if_pos zero]
    change 0 < 64 ∧ lowA.toNat < 2 ^ (64 - 0) ∧ lowB.toNat < 2 ^ (64 - 0)
    exact ⟨by decide, lowA.toNat_lt, lowB.toNat_lt⟩
  · rw [if_neg zero]
    have countBound := BitVec.clz_le (x := (highA ||| highB).toBitVec)
    change (highA ||| highB).toBitVec.clz.toNat ≤ 64 at countBound
    have jointBound : (highA.toNat ||| highB.toNat) <
        2 ^ (64 - (highA ||| highB).toBitVec.clz.toNat) := by
      simpa only [UInt64.toNat_toBitVec, UInt64.toNat_or] using
        (BitVec.toNat_lt_two_pow_sub_clz (x := (highA ||| highB).toBitVec))
    exact ⟨by change (highA ||| highB).toBitVec.clz.toNat < 64; omega, Nat.lt_of_le_of_lt Nat.left_le_or jointBound,
      Nat.lt_of_le_of_lt Nat.right_le_or jointBound⟩

theorem original_common_clz_window_derives_both_entire_aligned_word_values
    (highA highB lowA lowB : UInt64) :
    let w := sourceCommonWindow highA highB lowA lowB
    (sourceAlignedWindowWord w.highA lowA w.count).toNat =
        2 ^ w.count * w.highA.toNat + lowA.toNat / 2 ^ (64 - w.count) ∧
      (sourceAlignedWindowWord w.highB lowB w.count).toNat =
        2 ^ w.count * w.highB.toNat + lowB.toNat / 2 ^ (64 - w.count) := by
  have bounds := original_common_clz_window_derives_both_high_bounds_and_a_bounded_count highA highB lowA lowB
  exact ⟨original_aligned_window_word_has_its_entire_exact_nat_value
      _ _ _ bounds.1 bounds.2.1,
    original_aligned_window_word_has_its_entire_exact_nat_value
      _ _ _ bounds.1 bounds.2.2⟩

theorem original_zero_clz_fallback_returns_both_original_low_word_values
    (highA highB lowA lowB : UInt64)
    (zero : (highA ||| highB).toBitVec.clz.toNat = 64) :
    let w := sourceCommonWindow highA highB lowA lowB
    (sourceAlignedWindowWord w.highA lowA w.count).toNat = lowA.toNat ∧
      (sourceAlignedWindowWord w.highB lowB w.count).toNat = lowB.toNat := by
  have exactValues := original_common_clz_window_derives_both_entire_aligned_word_values highA highB lowA lowB
  dsimp only [sourceCommonWindow] at exactValues ⊢
  rw [if_pos zero] at exactValues ⊢
  simpa only [pow_zero, one_mul, Nat.sub_zero,
    Nat.div_eq_of_lt lowA.toNat_lt, Nat.div_eq_of_lt lowB.toNat_lt, add_zero] using exactValues

end ShielddSecurity.TransferBlstArmInverseWindowClz01

set_option pp.all true in
#check @ShielddSecurity.TransferBlstArmInverseWindowClz01.SourceCommonWindow
#print axioms ShielddSecurity.TransferBlstArmInverseWindowClz01.SourceCommonWindow

set_option pp.all true in
#check @ShielddSecurity.TransferBlstArmInverseWindowClz01.sourceCommonWindow
#print axioms ShielddSecurity.TransferBlstArmInverseWindowClz01.sourceCommonWindow

set_option pp.all true in
#check @ShielddSecurity.TransferBlstArmInverseWindowClz01.original_common_clz_window_derives_both_high_bounds_and_a_bounded_count
#print axioms ShielddSecurity.TransferBlstArmInverseWindowClz01.original_common_clz_window_derives_both_high_bounds_and_a_bounded_count

set_option pp.all true in
#check @ShielddSecurity.TransferBlstArmInverseWindowClz01.original_common_clz_window_derives_both_entire_aligned_word_values
#print axioms ShielddSecurity.TransferBlstArmInverseWindowClz01.original_common_clz_window_derives_both_entire_aligned_word_values

set_option pp.all true in
#check @ShielddSecurity.TransferBlstArmInverseWindowClz01.original_zero_clz_fallback_returns_both_original_low_word_values
#print axioms ShielddSecurity.TransferBlstArmInverseWindowClz01.original_zero_clz_fallback_returns_both_original_low_word_values
