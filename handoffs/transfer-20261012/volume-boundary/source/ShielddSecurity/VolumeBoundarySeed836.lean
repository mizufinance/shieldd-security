import ShielddSecurity.VolumeBoundaryLayout833
import ShielddSecurity.RegistryNaturalSeed298
import ShielddSecurity.TransferSem
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeBoundarySeed836
open ConcreteJubjubField01
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model

def borrow (w : TransferSem.Witness) : F :=
  BinaryComparison100.bit (BoundedLimbComparison119.borrow (w.volume.prior+(w.outputs 0).amount) w.registry.dailyLimit)
def seed (original : Nat → F) (w : TransferSem.Witness) (column : Nat) : F :=
  if column=7739 then (w.volume.dayStart:F) else if column=8255 then borrow w else original column

theorem day_start (original : Nat → F) (w : TransferSem.Witness) : seed original w 7739=(w.volume.dayStart:F) := rfl
theorem borrow_value (original : Nat → F) (w : TransferSem.Witness) : seed original w 8255=borrow w := by
  simp only [seed,show ¬(8255:Nat)=7739 by decide,if_false,if_true]
theorem outside (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (separate : column<7739 ∨ 8256≤column) : seed original w column=original column := by
  simp only [seed,if_neg (show column≠7739 by omega),if_neg (show column≠8255 by omega)]
theorem boolean (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (member : column∈VolumeBoundaryLayout833.flags) : seed original w column=0 ∨ seed original w column=1 := by
  have equal : column=8255 := by simpa only [VolumeBoundaryLayout833.flags,List.mem_singleton] using member
  subst column
  rw [borrow_value]
  unfold borrow BinaryComparison100.bit
  split <;> simp
end ShielddSecurity.VolumeBoundarySeed836

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundarySeed836.day_start
#print axioms ShielddSecurity.VolumeBoundarySeed836.day_start

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundarySeed836.borrow_value
#print axioms ShielddSecurity.VolumeBoundarySeed836.borrow_value

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundarySeed836.outside
#print axioms ShielddSecurity.VolumeBoundarySeed836.outside

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundarySeed836.boolean
#print axioms ShielddSecurity.VolumeBoundarySeed836.boolean
