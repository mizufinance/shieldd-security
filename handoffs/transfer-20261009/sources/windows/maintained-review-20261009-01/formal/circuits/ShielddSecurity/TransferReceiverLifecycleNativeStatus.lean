import ShielddSecurity.ShielddNativeReceiverLifecycle

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferReceiverLifecycleNativeStatus

/-- The circuit's Active integer predicate agrees with the owned native tags
and lifecycle guard, including generation and height. -/
theorem checked_of_legal (leaf : ShielddNativeReceiverLifecycle.Leaf)
    (legal : ReceiverLifecycle.LegalActive (ShielddNativeReceiverLifecycle.integer leaf)) :
    ShielddNativeReceiverLifecycle.activeChecked leaf = true := by
  cases status : leaf.status with
  | active =>
      have small := legal.2
      simp only [ShielddNativeReceiverLifecycle.integer,status,
        ShielddNativeReceiverLifecycle.Status.code] at small
      have height : leaf.height.val = 0 := by norm_num at small; omega
      simp [ShielddNativeReceiverLifecycle.activeChecked,
        ShielddNativeReceiverLifecycle.validate,status,height]
  | frozen =>
      have low := legal.1
      simp [ShielddNativeReceiverLifecycle.integer,status,
        ShielddNativeReceiverLifecycle.Status.code,Nat.add_mod,Nat.mul_mod] at low
  | seized =>
      have low := legal.1
      simp [ShielddNativeReceiverLifecycle.integer,status,
        ShielddNativeReceiverLifecycle.Status.code,Nat.add_mod,Nat.mul_mod] at low

/-- A bounded reconstructed integer identifies the same native lifecycle
field. No injectivity over arbitrary field representatives is assumed. -/
theorem checked_of_field {F Q : Type} [Field F] [CharP F Scalar.modulus]
    (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
    (power : ShielddNativeReceiverLifecycle.PowPrimitive (F := F) fq)
    (leaf : ShielddNativeReceiverLifecycle.Leaf) (n : Nat) (bound : n < 2^131)
    (meaning : (n : F) = ShielddNativeIvkHash.fqValue fq
      (ShielddNativeReceiverLifecycle.nativeField fq arithmetic initial power leaf))
    (legal : ReceiverLifecycle.LegalActive n) :
    ShielddNativeReceiverLifecycle.activeChecked leaf = true := by
  rw [ShielddNativeReceiverLifecycle.native_field_value fq arithmetic initial power leaf] at meaning
  have capacity : 2^131 < Scalar.modulus := by decide
  have same : n = ShielddNativeReceiverLifecycle.integer leaf :=
    bounded_cast_injective (F := F) (bound.trans capacity)
      ((ShielddNativeReceiverLifecycle.integer_bounded leaf).trans capacity) meaning
  apply checked_of_legal leaf
  simpa only [same] using legal

set_option pp.all true in
#check @checked_of_legal
#print axioms checked_of_legal
set_option pp.all true in
#check @checked_of_field
#print axioms checked_of_field

end ShielddSecurity.TransferReceiverLifecycleNativeStatus
