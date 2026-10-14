import ShielddSecurity.TierFlagWordFrame622
import ShielddSecurity.FieldZeroSeed125
import ShielddSecurity.RegistryNaturalSeed298
import ShielddSecurity.TransferSem
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierFlagSeed623
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def left (w : TransferSem.Witness) (index : Fin 4) : Nat :=
  (addressFields w.sender.address).getD index.val 0
def right (w : TransferSem.Witness) (index : Fin 4) : Nat :=
  (addressFields w.receiver.address).getD index.val 0
def delta (w : TransferSem.Witness) (index : Fin 4) : F :=
  (left w index:F)-(right w index:F)
def controls (original : Nat → F) (w : TransferSem.Witness) (column : Nat) : F :=
  if column=7605 then (if w.volume.useReal then 1 else 0)
  else if column=7606 then (if w.volume.startsNewDay then 1 else 0)
  else if column=7607 then (w.volume.context:F) else original column
def seed (original : Nat → F) (w : TransferSem.Witness) : Nat → F :=
  FieldZeroSeed125.seeded
    (FieldZeroSeed125.seeded
      (FieldZeroSeed125.seeded
        (FieldZeroSeed125.seeded (controls original w) 7603 (delta w ⟨3,by decide⟩))
        7601 (delta w ⟨2,by decide⟩))
      7599 (delta w ⟨1,by decide⟩))
    7597 (delta w ⟨0,by decide⟩)

theorem outside (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (separate : column<7597 ∨ 7608≤column) : seed original w column=original column := by
  unfold seed
  rw [FieldZeroSeed125.outside _ 7597 _ column (by omega),
    FieldZeroSeed125.outside _ 7599 _ column (by omega),
    FieldZeroSeed125.outside _ 7601 _ column (by omega),
    FieldZeroSeed125.outside _ 7603 _ column (by omega)]
  simp only [controls,if_neg (show column≠7605 by omega),
    if_neg (show column≠7606 by omega),if_neg (show column≠7607 by omega)]

theorem flag (original : Nat → F) (w : TransferSem.Witness) (index : Fin 4) :
    seed original w (7597+2*index.val)=FieldZeroSeed125.flag (delta w index) := by
  have cases : index=⟨0,by decide⟩ ∨ index=⟨1,by decide⟩ ∨
      index=⟨2,by decide⟩ ∨ index=⟨3,by decide⟩ := by
    have bound := index.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl <;> norm_num [seed,FieldZeroSeed125.seeded]

theorem inverse (original : Nat → F) (w : TransferSem.Witness) (index : Fin 4) :
    seed original w (7598+2*index.val)=(delta w index)⁻¹ := by
  have cases : index=⟨0,by decide⟩ ∨ index=⟨1,by decide⟩ ∨
      index=⟨2,by decide⟩ ∨ index=⟨3,by decide⟩ := by
    have bound := index.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl <;> norm_num [seed,FieldZeroSeed125.seeded]

theorem control_values (original : Nat → F) (w : TransferSem.Witness) :
    seed original w 7605=(if w.volume.useReal then 1 else 0) ∧
    seed original w 7606=(if w.volume.startsNewDay then 1 else 0) ∧
    seed original w 7607=(w.volume.context:F) := by
  norm_num [seed,FieldZeroSeed125.seeded,controls]

theorem flag_meaning (original : Nat → F) (w : TransferSem.Witness) (index : Fin 4)
    (leftBound : left w index<TransferCore.fieldModulus)
    (rightBound : right w index<TransferCore.fieldModulus) :
    seed original w (7597+2*index.val)=if left w index=right w index then 1 else 0 := by
  rw [flag]
  by_cases equal : left w index=right w index
  · simp [delta,equal,FieldZeroSeed125.flag]
  · have nonzero : delta w index≠0 := by
      intro zero
      have values := congrArg representation.value (sub_eq_zero.mp zero)
      rw [RegistryNaturalSeed298.represented_nat _ leftBound,
        RegistryNaturalSeed298.represented_nat _ rightBound] at values
      exact equal values
    simp only [FieldZeroSeed125.flag,if_neg nonzero,if_neg equal]

end ShielddSecurity.TierFlagSeed623
set_option pp.all true in
#check @ShielddSecurity.TierFlagSeed623.outside
#print axioms ShielddSecurity.TierFlagSeed623.outside
set_option pp.all true in
#check @ShielddSecurity.TierFlagSeed623.flag
#print axioms ShielddSecurity.TierFlagSeed623.flag
set_option pp.all true in
#check @ShielddSecurity.TierFlagSeed623.inverse
#print axioms ShielddSecurity.TierFlagSeed623.inverse
set_option pp.all true in
#check @ShielddSecurity.TierFlagSeed623.control_values
#print axioms ShielddSecurity.TierFlagSeed623.control_values
set_option pp.all true in
#check @ShielddSecurity.TierFlagSeed623.flag_meaning
#print axioms ShielddSecurity.TierFlagSeed623.flag_meaning
