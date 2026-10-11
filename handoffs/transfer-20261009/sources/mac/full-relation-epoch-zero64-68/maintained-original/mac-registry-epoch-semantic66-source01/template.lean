import ShielddSecurity.TransferSem
import ShielddSecurity.CapturedGlobalEpoch64
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryEpoch66
open CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]
theorem registry_epoch_bound (c : TransferSem.Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.RegistrySem c w) : w.registry.audit.epoch<2^64 :=
  legal.2.2.2.2.1
theorem registry_epoch_nonzero (c : TransferSem.Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.RegistrySem c w) (regulated : w.regulated=true) :
    w.registry.audit.epoch≠0 := by
  have branch:=legal.2.2.2.2.2.2.2.2.2.2
  rw [regulated] at branch
  exact branch.2.1
theorem cast_epoch_zero (n : Nat) (bound : n<2^64) (zero : (n : F)=0) : n=0 := by
  have canonical : n<p := lt_trans bound (by decide)
  exact (CapturedEpochHints62.cast_small_unique n 0 canonical (by decide) (by simpa only [Nat.cast_zero] using zero))
theorem registry_guard (c : TransferSem.Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.RegistrySem c w) (base : Nat → F)
    (epoch : base 34=(w.registry.audit.epoch : F))
    (regulated : base 10=(if w.regulated then 1 else 0)) : base 34=0 → base 10=0 := by
  intro isZero
  have natZero:=cast_epoch_zero w.registry.audit.epoch (registry_epoch_bound c w legal) (epoch.symm.trans isZero)
  cases bit : w.regulated with
  | false => simpa only [bit] using regulated
  | true => exact False.elim ((registry_epoch_nonzero c w legal bit) natZero)
theorem legal_epoch_completion (c : TransferSem.Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.RegistrySem c w) (base : Nat → F)
    (epoch : base 34=(w.registry.audit.epoch : F))
    (regulated : base 10=(if w.regulated then 1 else 0)) (zero : base 0=1) :
    SatisfiesAt (CapturedGlobalEpoch64.completed base w.registry.audit.epoch)
      CapturedEpochRange60.block.actual 65 ∧
    SatisfiesAt (CapturedGlobalEpoch64.completed base w.registry.audit.epoch)
      CapturedEpochNonzero61.assertionBlock.actual 4 :=
  CapturedGlobalEpoch64.completed_epoch_assertions base w.registry.audit.epoch
    (registry_epoch_bound c w legal) epoch (registry_guard c w legal base epoch regulated) zero
theorem legal_epoch_arithmetic (base : Nat → F) (w : TransferSem.Witness) :
    CompilerArithmeticBlock44.SatisfiesAt
      (CapturedGlobalEpoch64.completed base w.registry.audit.epoch)
      CapturedFullArithmetic52.rowAt 177954 :=
  CapturedGlobalEpoch64.completed_arithmetic base w.registry.audit.epoch
end ShielddSecurity.CapturedRegistryEpoch66
