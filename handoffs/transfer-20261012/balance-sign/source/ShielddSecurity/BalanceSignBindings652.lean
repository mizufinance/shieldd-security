import ShielddSecurity.BalanceSignRetained651
import ShielddSecurity.TierFlagBindings630
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceSignBindings652
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def negative (w : TransferSem.Witness) : Bool :=
  decide ((w.spends 0).amount+(w.spends 1).amount < (w.outputs 0).amount+(w.outputs 1).amount)
def seed (original : Nat → F) (w : TransferSem.Witness) (column : Nat) : F :=
  if column=21711 then (if negative w then 1 else 0) else original column

theorem outside (original : Nat → F) (w : TransferSem.Witness) (column : Nat) (different : column≠21711) :
    seed original w column=original column := by simp only [seed,if_neg different]

theorem selected (original : Nat → F) (w : TransferSem.Witness) :
    seed original w 21711=if negative w then 1 else 0 := by rfl

theorem sign_boolean (original : Nat → F) (w : TransferSem.Witness) :
    seed original w 21711=0 ∨ seed original w 21711=1 := by
  rw [selected]
  cases negative w <;> simp

def assignment (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  TierFlagBindings630.assignment (seed original w) c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem flag (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 21711=
      if negative w then 1 else 0 := by
  have preserved := TierFlagSeed623.outside (seed original w) w 21711 (Or.inr (by decide))
  have boolean : TierFlagSeed623.seed (seed original w) w 21711=0 ∨
      TierFlagSeed623.seed (seed original w) w 21711=1 := by
    rw [preserved]
    exact sign_boolean original w
  unfold assignment TierFlagBindings630.assignment
  exact (BalanceSignRetained651.tier_frame _ c w legal rkInitial authInitial initial
    senderInitial receiverInitial 21711 (by decide +kernel) (fun _ => boolean)).trans
    (preserved.trans (selected original w))

theorem signed_magnitude (w : TransferSem.Witness) :
    (if negative w then -(RemainingWordSeed369.magnitude w:F) else (RemainingWordSeed369.magnitude w:F))=
      (((w.spends 0).amount+(w.spends 1).amount:F)-((w.outputs 0).amount+(w.outputs 1).amount:F)) := by
  unfold negative RemainingWordSeed369.magnitude
  dsimp only
  by_cases small : (w.spends 0).amount+(w.spends 1).amount < (w.outputs 0).amount+(w.outputs 1).amount
  · have ordered : ¬((w.outputs 0).amount+(w.outputs 1).amount≤(w.spends 0).amount+(w.spends 1).amount) := by omega
    simp only [small,decide_true,if_true,ordered,if_false]
    rw [Nat.cast_sub (by omega : (w.spends 0).amount+(w.spends 1).amount≤(w.outputs 0).amount+(w.outputs 1).amount)]
    push_cast
    ring
  · have ordered : (w.outputs 0).amount+(w.outputs 1).amount≤(w.spends 0).amount+(w.spends 1).amount := by omega
    simp only [small,decide_false,Bool.false_eq_true,if_false,ordered,if_true]
    rw [Nat.cast_sub ordered]
    push_cast
    ring
end ShielddSecurity.BalanceSignBindings652

set_option pp.all true in
#check @ShielddSecurity.BalanceSignBindings652.outside
#print axioms ShielddSecurity.BalanceSignBindings652.outside

set_option pp.all true in
#check @ShielddSecurity.BalanceSignBindings652.selected
#print axioms ShielddSecurity.BalanceSignBindings652.selected

set_option pp.all true in
#check @ShielddSecurity.BalanceSignBindings652.sign_boolean
#print axioms ShielddSecurity.BalanceSignBindings652.sign_boolean

set_option pp.all true in
#check @ShielddSecurity.BalanceSignBindings652.flag
#print axioms ShielddSecurity.BalanceSignBindings652.flag

set_option pp.all true in
#check @ShielddSecurity.BalanceSignBindings652.signed_magnitude
#print axioms ShielddSecurity.BalanceSignBindings652.signed_magnitude
