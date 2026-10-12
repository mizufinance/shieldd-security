import ShielddSecurity.TransferCommonwareSqrtSchedule01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCommonwareSqrtWords01
open TransferCommonwareSqrtSearch01
open TransferCommonwareSqrtSchedule01
variable {F : Type} [Field F] [DecidableEq F]

theorem actual_commonware_successful_search_derives_safe_unsigned_correction_subtraction
    (m i : Nat) (value : F) (bounded : m ≤ 32) (success : sourceSearch m value = some i) :
    ((UInt32.ofNat m)-(UInt32.ofNat i)-1).toNat = m-i-1 := by
  have inside := every_successful_source_search_returns_an_index_below_m m i value success
  have wordSize : UInt32.size = 4294967296 := rfl
  have mBound : m < UInt32.size := by rw [wordSize]; omega
  have iBound : i < UInt32.size := by rw [wordSize]; omega
  have mValue := UInt32.toNat_ofNat_of_lt' mBound
  have iValue := UInt32.toNat_ofNat_of_lt' iBound
  have order : UInt32.ofNat i ≤ UInt32.ofNat m := by
    rw [UInt32.le_iff_toNat_le,mValue,iValue]
    omega
  have remaining : ((UInt32.ofNat m)-(UInt32.ofNat i)).toNat = m-i := by
    rw [UInt32.toNat_sub_of_le _ _ order,mValue,iValue]
  have positive : (1 : UInt32) ≤ (UInt32.ofNat m)-(UInt32.ofNat i) := by
    rw [UInt32.le_iff_toNat_le,remaining]
    change 1 ≤ m-i
    omega
  rw [UInt32.toNat_sub_of_le _ _ positive,remaining]
  rfl

set_option pp.all true in
#check @actual_commonware_successful_search_derives_safe_unsigned_correction_subtraction
#print axioms actual_commonware_successful_search_derives_safe_unsigned_correction_subtraction
end ShielddSecurity.TransferCommonwareSqrtWords01
