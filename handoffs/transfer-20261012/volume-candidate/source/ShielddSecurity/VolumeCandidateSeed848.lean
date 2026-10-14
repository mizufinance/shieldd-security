import ShielddSecurity.VolumeCandidateLayout846
import ShielddSecurity.RegistryNaturalSeed298
import ShielddSecurity.TransferSem
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeCandidateSeed848
open ConcreteJubjubField01
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model
def candidate (w : TransferSem.Witness) : Nat := w.volume.prior+(w.outputs 0).amount
def flag (w : TransferSem.Witness) (index : Nat) : Bool := (encodeBits 128 (candidate w))[index]?.getD false
def seed (original : Nat → F) (w : TransferSem.Witness) (column : Nat) : F :=
  if 8127≤column ∧ column<8255 then BooleanHints207.bitValue (flag w (column-8127)) else original column
theorem selected (original : Nat → F) (w : TransferSem.Witness) (index : Nat) (bound : index<128) :
    seed original w (8127+index)=BooleanHints207.bitValue (flag w index) := by
  rw [seed,if_pos (by omega),Nat.add_sub_cancel_left]
theorem outside (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (separate : column<8127 ∨ 8255≤column) : seed original w column=original column := by
  rw [seed,if_neg (by omega)]
theorem boolean (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (member : column∈VolumeCandidateLayout846.flags) : seed original w column=0 ∨ seed original w column=1 := by
  have bound := VolumeCandidateLayout846.bounds column member
  rw [seed,if_pos bound]
  unfold BooleanHints207.bitValue
  split <;> simp
end ShielddSecurity.VolumeCandidateSeed848

set_option pp.all true in
#check @ShielddSecurity.VolumeCandidateSeed848.selected
#print axioms ShielddSecurity.VolumeCandidateSeed848.selected

set_option pp.all true in
#check @ShielddSecurity.VolumeCandidateSeed848.outside
#print axioms ShielddSecurity.VolumeCandidateSeed848.outside

set_option pp.all true in
#check @ShielddSecurity.VolumeCandidateSeed848.boolean
#print axioms ShielddSecurity.VolumeCandidateSeed848.boolean
