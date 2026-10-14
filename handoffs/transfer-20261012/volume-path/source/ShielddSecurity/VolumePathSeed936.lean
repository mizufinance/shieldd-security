import ShielddSecurity.VolumePathLayout933
import ShielddSecurity.RegistryNaturalSeed298
import ShielddSecurity.TransferSem
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePathSeed936
open ConcreteJubjubField01
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model
def value (w : TransferSem.Witness) (column : Nat) : F :=
  if h : column∈VolumePathLayout933.columns then
    (w.volume.priorSiblings ⟨(column-8388)/3,by have b:=VolumePathLayout933.bounds column h;omega⟩ ⟨(column-8388)%3,by omega⟩:F)
  else 0
def seed (original : Nat → F) (w : TransferSem.Witness) (column : Nat) : F :=
  if column∈VolumePathLayout933.columns then value w column else original column
theorem sibling (original : Nat → F) (w : TransferSem.Witness) (level : Fin 24) (slot : Fin 3) :
    seed original w (8388+3*level.val+slot.val)=(w.volume.priorSiblings level slot:F) := by
  have member : 8388+3*level.val+slot.val∈VolumePathLayout933.columns := by
    exact List.mem_range'.mpr ⟨3*level.val+slot.val,by omega,by omega⟩
  have quotient : (8388+3*level.val+slot.val-8388)/3=level.val := by omega
  have remainder : (8388+3*level.val+slot.val-8388)%3=slot.val := by omega
  simp only [seed,if_pos member,value,dif_pos member]
  exact congrArg (fun n : Nat => (n:F))
    (congrArg₂ w.volume.priorSiblings (Fin.ext quotient) (Fin.ext remainder))
theorem outside (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (separate : column<8388 ∨ 8460≤column) : seed original w column=original column := by
  rw [seed,if_neg (by intro member;have bounds:=VolumePathLayout933.bounds column member;omega)]
theorem boolean (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (member : column∈VolumePathLayout933.flags) : seed original w column=0 ∨ seed original w column=1 := by
  simp only [VolumePathLayout933.flags,List.not_mem_nil] at member
end ShielddSecurity.VolumePathSeed936

set_option pp.all true in
#check @ShielddSecurity.VolumePathSeed936.sibling
#print axioms ShielddSecurity.VolumePathSeed936.sibling

set_option pp.all true in
#check @ShielddSecurity.VolumePathSeed936.outside
#print axioms ShielddSecurity.VolumePathSeed936.outside

set_option pp.all true in
#check @ShielddSecurity.VolumePathSeed936.boolean
#print axioms ShielddSecurity.VolumePathSeed936.boolean
