import ShielddSecurity.CapturedRegistryValueRange97
import ShielddSecurity.CapturedRegulatedAsset96
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryValueFrame98
open CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F]
abbrev completed (base : Nat → F) (initial : Fin 4 → Group.Point F) (n epoch position : Nat) : Nat → F :=
  CapturedGlobalSubgroup90.completed (CapturedRegistryValueRange97.completed base n) initial epoch position


set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryValueFrame98.completed
#print axioms ShielddSecurity.CapturedRegistryValueFrame98.completed
theorem truth_frame (rho sigma : Nat → F) (eleven : rho 11=sigma 11)
    (bits : ∀ index<255,rho (216+index)=sigma (216+index))
    (truth : TruthAt rho CapturedRegistryValueRange97.block.recipe 256) :
    TruthAt sigma CapturedRegistryValueRange97.block.recipe 256 := by
  have parts:=(CapturedRegistryValueRange97.truth_iff rho).mp truth
  apply (CapturedRegistryValueRange97.truth_iff sigma).mpr
  constructor
  · intro index bound
    rw [←bits index bound]
    exact parts.1 index bound
  · have same : CapturedRegistryValueRange97.columns.map rho=CapturedRegistryValueRange97.columns.map sigma := by
      apply List.map_congr_left
      intro column member
      change column∈List.range' 216 255 at member
      obtain ⟨index,bound,same⟩:=List.mem_range'.mp member
      simp only [one_mul] at same
      subst column
      exact bits index bound
    rw [←same,←eleven]
    exact parts.2


set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryValueFrame98.truth_frame
#print axioms ShielddSecurity.CapturedRegistryValueFrame98.truth_frame
theorem bits_frame (base : Nat → F) (initial : Fin 4 → Group.Point F) (n epoch position index : Nat)
    (bound : index<255) : completed base initial n epoch position (216+index)=
      CapturedRegistryValueRange97.completed base n (216+index) := by
  have small : 216+index<22738 := by omega
  have notVerifier : 216+index≠1 ∧ 216+index≠2 ∧ 216+index≠copy := by
    have c : copy=200692 := rfl
    omega
  have notEpoch : ¬(49≤216+index ∧ 216+index<135) := by omega
  have notPosition : 216≤216+index := by omega
  have seedSmall : ∀ column∈CapturedFourSubgroupSeed89.hintColumns,column<216 := by decide
  have notSeed : 216+index∉CapturedFourSubgroupSeed89.hintColumns := by
    intro member
    have h:=seedSmall (216+index) member
    omega
  exact (CapturedGlobalPosition77.outside
    (CapturedFourSubgroupSeed89.seeded (CapturedRegistryValueRange97.completed base n) initial)
    epoch position (216+index) (Or.inl small) notVerifier notEpoch (Or.inr notPosition)).trans
      (CapturedFourSubgroupSeed89.seeded_outside _ initial _ notSeed)


set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryValueFrame98.bits_frame
#print axioms ShielddSecurity.CapturedRegistryValueFrame98.bits_frame
theorem eleven_frame (base : Nat → F) (initial : Fin 4 → Group.Point F) (n epoch position : Nat) :
    completed base initial n epoch position 11=CapturedRegistryValueRange97.completed base n 11 :=
  CapturedRegulatedAsset96.outside_early _ initial epoch position 11 (by decide) (by decide) (by decide)

variable [CharP F p]

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryValueFrame98.eleven_frame
#print axioms ShielddSecurity.CapturedRegistryValueFrame98.eleven_frame
theorem range_assertions (base : Nat → F) (initial : Fin 4 → Group.Point F) (n epoch position : Nat)
    (bound : n<2^255) (meaning : base 11=(n:F)) :
    SatisfiesAt (completed base initial n epoch position)
      (fun index => CapturedFullRelation58.rowAt (178119+index)) 256 := by
  have truth:=truth_frame (CapturedRegistryValueRange97.completed base n) (completed base initial n epoch position)
    (eleven_frame base initial n epoch position).symm
    (fun index h => (bits_frame base initial n epoch position index h).symm)
    (CapturedRegistryValueRange97.completed_truth base n bound meaning)
  have linked : completed base initial n epoch position copy=completed base initial n epoch position 0 :=
    CapturedGlobalRegistered74.completed_copy _ _
  have rows:=(CompilerAssertionBlock51.satisfies_iff copy 256 CapturedRegistryValueRange97.block _ linked).mpr truth
  intro index before row found
  change CapturedFullRelation58.rowAt (178119+index)=some row at found
  rw [CapturedRegistryValueRange97.full_position index before] at found
  exact rows index before row found


set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryValueFrame98.range_assertions
#print axioms ShielddSecurity.CapturedRegistryValueFrame98.range_assertions
theorem modulus_bound : p<2^255 := by decide


set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryValueFrame98.modulus_bound
#print axioms ShielddSecurity.CapturedRegistryValueFrame98.modulus_bound
theorem legal_range (c : TransferSem.Crypto) (w : TransferSem.Witness) (legal : TransferSem.RegistrySem c w)
    (base : Nat → F) (initial : Fin 4 → Group.Point F) (meaning : base 11=(w.registry.value:F)) :
    SatisfiesAt (completed base initial w.registry.value w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178119+index)) 256 :=
  range_assertions base initial _ _ _ (Nat.lt_trans legal.2.2.2.2.2.2.1 modulus_bound) meaning
end ShielddSecurity.CapturedRegistryValueFrame98

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryValueFrame98.legal_range
#print axioms ShielddSecurity.CapturedRegistryValueFrame98.legal_range
