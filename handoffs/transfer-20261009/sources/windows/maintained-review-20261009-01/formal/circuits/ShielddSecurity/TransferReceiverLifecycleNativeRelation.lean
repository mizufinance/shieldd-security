import ShielddSecurity.TransferReceiverLifecycleStatusSoundness
import ShielddSecurity.TransferReceiverLifecycleNativeStatus

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferReceiverLifecycleNativeRelation

variable {F Q : Type} [Field F] [CharP F Scalar.modulus]

/-- The actual enabled gate rows and the reconstructed same word force the
owned native receiver leaf to be Active and pass lifecycle validation. -/
theorem sound (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
    (power : ShielddNativeReceiverLifecycle.PowPrimitive (F := F) fq)
    (leaf : ShielddNativeReceiverLifecycle.Leaf) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (flag : Bool) (flagMeaning : rho 10 = if flag then 1 else 0)
    (inputMeaning : rho 1767 = ShielddNativeIvkHash.fqValue fq
      (ShielddNativeReceiverLifecycle.nativeField fq arithmetic initial power leaf))
    (satisfied : Satisfies rho TransferReceiverLifecycleStatusSoundness.rows) :
    flag = true → ShielddNativeReceiverLifecycle.activeChecked leaf = true := by
  intro enabled
  have flagOne : rho 10 = 1 := by simpa only [enabled,if_true] using flagMeaning
  obtain ⟨n,bound,meaning,legal⟩ := TransferReceiverLifecycleStatusSoundness.sound rho one four flagOne satisfied
  exact TransferReceiverLifecycleNativeStatus.checked_of_field fq arithmetic initial power leaf n bound
    (meaning.trans inputMeaning) legal

/-- Native legal inputs supply the same bounded integer and enabled-status
predicate consumed by the constructive range and product proofs. -/
theorem legal_input (leaf : ShielddNativeReceiverLifecycle.Leaf) (flag : Bool)
    (checked : flag = true → ShielddNativeReceiverLifecycle.activeChecked leaf = true) :
    ShielddNativeReceiverLifecycle.integer leaf < 2^131 ∧
      (flag = true → ReceiverLifecycle.LegalActive (ShielddNativeReceiverLifecycle.integer leaf)) := by
  exact ⟨ShielddNativeReceiverLifecycle.integer_bounded leaf,
    fun enabled => ShielddNativeReceiverLifecycle.active_legal leaf (checked enabled)⟩

set_option pp.all true in
#check @sound
#print axioms sound
set_option pp.all true in
#check @legal_input
#print axioms legal_input

end ShielddSecurity.TransferReceiverLifecycleNativeRelation
