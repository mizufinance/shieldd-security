import ShielddSecurity.VolumeHashLayout883
import ShielddSecurity.RegistryNaturalSeed298
import ShielddSecurity.TransferSem
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeHashSeed886
open ConcreteJubjubField01
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model
def value (w : TransferSem.Witness) (column : Nat) : F :=
  if column=7740 then (w.volume.subject:F) else if column=8385 then (w.volume.priorBlinding:F) else if column=8386 then (w.volume.priorCommitment:F) else if column=8508 then (w.volume.successorBlinding:F) else if column=8509 then (w.volume.nullifier:F) else if column=8510 then (w.volume.commitment:F) else 0
def seed (original : Nat → F) (w : TransferSem.Witness) (column : Nat) : F :=
  if column∈VolumeHashLayout883.columns then value w column else original column
theorem subject (original : Nat → F) (w : TransferSem.Witness) : seed original w 7740=(w.volume.subject:F) := by simp [seed,value,VolumeHashLayout883.columns]
theorem priorBlinding (original : Nat → F) (w : TransferSem.Witness) : seed original w 8385=(w.volume.priorBlinding:F) := by simp [seed,value,VolumeHashLayout883.columns]
theorem priorCommitment (original : Nat → F) (w : TransferSem.Witness) : seed original w 8386=(w.volume.priorCommitment:F) := by simp [seed,value,VolumeHashLayout883.columns]
theorem successorBlinding (original : Nat → F) (w : TransferSem.Witness) : seed original w 8508=(w.volume.successorBlinding:F) := by simp [seed,value,VolumeHashLayout883.columns]
theorem nullifier (original : Nat → F) (w : TransferSem.Witness) : seed original w 8509=(w.volume.nullifier:F) := by simp [seed,value,VolumeHashLayout883.columns]
theorem commitment (original : Nat → F) (w : TransferSem.Witness) : seed original w 8510=(w.volume.commitment:F) := by simp [seed,value,VolumeHashLayout883.columns]
theorem outside (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (separate : column<7740 ∨ 8511≤column) : seed original w column=original column := by
  rw [seed,if_neg (by intro member;have bounds:=VolumeHashLayout883.bounds column member;omega)]
theorem boolean (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (member : column∈VolumeHashLayout883.flags) : seed original w column=0 ∨ seed original w column=1 := by
  simp only [VolumeHashLayout883.flags,List.not_mem_nil] at member
end ShielddSecurity.VolumeHashSeed886

set_option pp.all true in
#check @ShielddSecurity.VolumeHashSeed886.subject
#print axioms ShielddSecurity.VolumeHashSeed886.subject

set_option pp.all true in
#check @ShielddSecurity.VolumeHashSeed886.priorBlinding
#print axioms ShielddSecurity.VolumeHashSeed886.priorBlinding

set_option pp.all true in
#check @ShielddSecurity.VolumeHashSeed886.priorCommitment
#print axioms ShielddSecurity.VolumeHashSeed886.priorCommitment

set_option pp.all true in
#check @ShielddSecurity.VolumeHashSeed886.successorBlinding
#print axioms ShielddSecurity.VolumeHashSeed886.successorBlinding

set_option pp.all true in
#check @ShielddSecurity.VolumeHashSeed886.nullifier
#print axioms ShielddSecurity.VolumeHashSeed886.nullifier

set_option pp.all true in
#check @ShielddSecurity.VolumeHashSeed886.commitment
#print axioms ShielddSecurity.VolumeHashSeed886.commitment

set_option pp.all true in
#check @ShielddSecurity.VolumeHashSeed886.outside
#print axioms ShielddSecurity.VolumeHashSeed886.outside

set_option pp.all true in
#check @ShielddSecurity.VolumeHashSeed886.boolean
#print axioms ShielddSecurity.VolumeHashSeed886.boolean
