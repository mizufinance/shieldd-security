import ShielddSecurity.TransferReceiverLifecycleNativeRelation
import ShielddSecurity.TransferReceiverLifecycleCompletion

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferReceiverLifecycleNativeCompletion

variable {F Q : Type} [Field F] [CharP F Scalar.modulus]

/-- Both compositions retain the same captured range and gate blocks. -/
theorem row_identity : TransferReceiverLifecycleCompletion.rows =
    TransferReceiverLifecycleStatusSoundness.rows := rfl

/-- A native legal leaf supplies the bounded word used by the actual row
constructor; no satisfying assignment is an input to this theorem. -/
theorem complete (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
    (power : ShielddNativeReceiverLifecycle.PowPrimitive (F := F) fq)
    (leaf : ShielddNativeReceiverLifecycle.Leaf) (base : Nat → F)
    (one : base 0 = 1) (linked : base 200692 = base 0)
    (flag : Bool) (flagMeaning : base 10 = if flag then 1 else 0)
    (inputMeaning : base 1767 = ShielddNativeIvkHash.fqValue fq
      (ShielddNativeReceiverLifecycle.nativeField fq arithmetic initial power leaf))
    (checked : flag = true → ShielddNativeReceiverLifecycle.activeChecked leaf = true) :
    Satisfies (TransferReceiverLifecycleCompletion.completed base
      (ShielddNativeReceiverLifecycle.integer leaf)) TransferReceiverLifecycleStatusSoundness.rows := by
  have legal := TransferReceiverLifecycleNativeRelation.legal_input leaf flag checked
  have meaning := inputMeaning.trans
    (ShielddNativeReceiverLifecycle.native_field_value fq arithmetic initial power leaf)
  rw [← row_identity]
  exact TransferReceiverLifecycleCompletion.complete base one linked
    (ShielddNativeReceiverLifecycle.integer leaf) legal.1 meaning flag flagMeaning legal.2

/-- Construction preserves the encoded input, enable flag, and constant link. -/
theorem preserved_inputs (base : Nat → F) (leaf : ShielddNativeReceiverLifecycle.Leaf)
    (column : Nat) (input : column ∈ ([0,10,1767,200692] : List Nat)) :
    TransferReceiverLifecycleCompletion.completed base
      (ShielddNativeReceiverLifecycle.integer leaf) column = base column := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at input
  rcases input with rfl | rfl | rfl | rfl
  all_goals exact TransferReceiverLifecycleCompletion.preserved base _ _ (by decide)

set_option pp.all true in
#check @row_identity
#print axioms row_identity
set_option pp.all true in
#check @complete
#print axioms complete
set_option pp.all true in
#check @preserved_inputs
#print axioms preserved_inputs

end ShielddSecurity.TransferReceiverLifecycleNativeCompletion
