import ShielddSecurity.UserLifecycleWord345
import ShielddSecurity.CapturedSenderLifecycle346
import ShielddSecurity.CapturedReceiverLifecycle347
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedUserLifecycle348
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open UserLifecycleWord345

theorem bit_index_bound (index : Nat) (bound : index<67) : bitIndex index<131 := by
  unfold bitIndex
  split <;> omega

theorem sender_zero (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w)
    (index : Nat) (bound : index<67) : assignment original c w initial (CapturedSenderLifecycle346.output index)=0 := by
  have value := CapturedSenderLifecycle346.products (assignment original c w initial)
    (SharedHighZeroRows333.arithmetic (UserWordSeed342.seed original w) c w initial)
    (SharedComparisonBlocks327.linked (HighZeroSeed329.seed (UserWordSeed342.seed original w) w) c w initial) index bound
  change assignment original c w initial (CapturedSenderLifecycle346.output index)=
    assignment original c w initial 10*(assignment original c w initial (1611+bitIndex index)-
      (if index=0 then assignment original c w initial 0 else 0)) at value
  have one := SharedHighZeroRows333.zero (UserWordSeed342.seed original w) c w initial
  change assignment original c w initial 0=1 at one
  rw [control original c w initial,sender_bits original c w initial legal (bitIndex index) (bit_index_bound index bound),
    one] at value
  have user := legal.2.1.2.1
  have active : w.regulated=true → w.sender.lifecycle%8=1 ∧ w.sender.lifecycle/2^67=0 := by
    intro enabled
    have branch := user.2.2.2.2.2.2.2.2 enabled
    exact ⟨branch.1,branch.2.1⟩
  exact value.trans (gated_bit w.regulated w.sender.lifecycle index bound active)

theorem sender_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    CompilerAssertionBlock51.SatisfiesAt (assignment original c w initial)
      (fun index => CapturedFullRelation58.rowAt (177954+1657+index)) 67 :=
  CapturedSenderLifecycle346.complete (assignment original c w initial) (sender_zero original c w initial legal)

theorem receiver_zero (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w)
    (index : Nat) (bound : index<67) : assignment original c w initial (CapturedReceiverLifecycle347.output index)=0 := by
  have value := CapturedReceiverLifecycle347.products (assignment original c w initial)
    (SharedHighZeroRows333.arithmetic (UserWordSeed342.seed original w) c w initial)
    (SharedComparisonBlocks327.linked (HighZeroSeed329.seed (UserWordSeed342.seed original w) w) c w initial) index bound
  change assignment original c w initial (CapturedReceiverLifecycle347.output index)=
    assignment original c w initial 10*(assignment original c w initial (1849+bitIndex index)-
      (if index=0 then assignment original c w initial 0 else 0)) at value
  have one := SharedHighZeroRows333.zero (UserWordSeed342.seed original w) c w initial
  change assignment original c w initial 0=1 at one
  rw [control original c w initial,receiver_bits original c w initial legal (bitIndex index) (bit_index_bound index bound),
    one] at value
  have user := legal.2.1.2.2.1
  have active : w.regulated=true → w.receiver.lifecycle%8=1 ∧ w.receiver.lifecycle/2^67=0 := by
    intro enabled
    have branch := user.2.2.2.2.2.2.2.2 enabled
    exact ⟨branch.1,branch.2.1⟩
  exact value.trans (gated_bit w.regulated w.receiver.lifecycle index bound active)

theorem receiver_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    CompilerAssertionBlock51.SatisfiesAt (assignment original c w initial)
      (fun index => CapturedFullRelation58.rowAt (177954+1912+index)) 67 :=
  CapturedReceiverLifecycle347.complete (assignment original c w initial) (receiver_zero original c w initial legal)

def Rows (rho : Nat → F) : Prop :=
  CompilerAssertionBlock51.SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (177954+1657+index)) 67 ∧
  CompilerAssertionBlock51.SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (177954+1912+index)) 67

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    Rows (assignment original c w initial) :=
  ⟨sender_rows original c w initial legal,receiver_rows original c w initial legal⟩
end ShielddSecurity.SharedUserLifecycle348

set_option pp.all true in
#check @ShielddSecurity.SharedUserLifecycle348.bit_index_bound
#print axioms ShielddSecurity.SharedUserLifecycle348.bit_index_bound

set_option pp.all true in
#check @ShielddSecurity.SharedUserLifecycle348.sender_zero
#print axioms ShielddSecurity.SharedUserLifecycle348.sender_zero

set_option pp.all true in
#check @ShielddSecurity.SharedUserLifecycle348.sender_rows
#print axioms ShielddSecurity.SharedUserLifecycle348.sender_rows

set_option pp.all true in
#check @ShielddSecurity.SharedUserLifecycle348.receiver_zero
#print axioms ShielddSecurity.SharedUserLifecycle348.receiver_zero

set_option pp.all true in
#check @ShielddSecurity.SharedUserLifecycle348.receiver_rows
#print axioms ShielddSecurity.SharedUserLifecycle348.receiver_rows

set_option pp.all true in
#check @ShielddSecurity.SharedUserLifecycle348.Rows
#print axioms ShielddSecurity.SharedUserLifecycle348.Rows

set_option pp.all true in
#check @ShielddSecurity.SharedUserLifecycle348.all_rows
#print axioms ShielddSecurity.SharedUserLifecycle348.all_rows
