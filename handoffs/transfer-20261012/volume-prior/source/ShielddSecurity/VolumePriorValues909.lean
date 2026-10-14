import ShielddSecurity.VolumeHashAssignment892
import ShielddSecurity.RoutingParameterValues879
import ShielddSecurity.VolumePriorHash908
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePriorValues909
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumeHashAssignment892 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model SatisfiesAt
  PoseidonNatural192.hash Poseidon.hash6 TransferSem.volumeState RoutingParameterAssignment872.assignment
  VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment
  SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem day_start : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 7739=(w.volume.dayStart:F) := by
  unfold assignment RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment
  exact VolumeBoundaryAssignment842.day_start _ u c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem prior : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 7741=(w.volume.prior:F) := by
  unfold assignment RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment
  exact VolumeTransitionBindings827.words _ u c w legal rkInitial authInitial initial senderInitial receiverInitial 7741 (by decide +kernel)

theorem starts_new_day : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 7606=(if w.volume.startsNewDay then 1 else 0) := by
  unfold assignment RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment
  exact VolumeTransitionBindings827.starts_new_day _ u c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem natural_hash (c : Crypto) (w : TransferSem.Witness) :
    ((BalanceBlindingDomain670.crypto c).hash .volumeState [w.volume.subject,w.volume.dayStart,w.volume.prior,w.volume.priorBlinding]:F)=
    Poseidon.hash6 (Poseidon.castParameters VolumePriorHash908.parameters) 5
      [(w.volume.subject:F),(w.volume.dayStart:F),(w.volume.prior:F),(w.volume.priorBlinding:F)] := by
  change (PoseidonNatural192.hash RegistryNatural193.small RegistryNatural193.wide ConcreteRegistrySharedEncoding294.representation
    .volumeState [w.volume.subject,w.volume.dayStart,w.volume.prior,w.volume.priorBlinding]:F)=_
  rw [show Poseidon.castParameters VolumePriorHash908.parameters=(RegistryNatural193.wide : Poseidon.Parameters F 6) from rfl]
  rw [PoseidonNatural192.hash_cast]
  unfold Poseidon.hash
  rw [if_neg (by change ¬4≤2;decide)]
  rfl

theorem generic_hash {G : Type} [Field G] [CharP G CapturedInitial73419Generic01.p]
    (rho : Nat → G) (subject day amount blinding : G)
    (zero : rho 0=1) (copied : rho CapturedInitial73419Generic01.copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (subjectValue : rho 7740=subject) (dayValue : rho 7739=day)
    (amountValue : rho 7741=amount) (blindingValue : rho 8385=blinding) :
    eval rho VolumePriorHash908.result=Poseidon.hash6 (Poseidon.castParameters VolumePriorHash908.parameters) 5
      [subject,day,amount,blinding] := by
  have result := VolumePriorHash908.hash rho zero (copied.trans zero.symm) arithmetic
  rw [subjectValue,dayValue,amountValue,blindingValue] at result
  exact result

theorem state_eq (c : Crypto) (subject day amount blinding : Nat) :
    volumeState c subject day amount blinding=c.hash .volumeState [subject,day,amount,blinding] := by simp only [volumeState]

theorem hash_value : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) VolumePriorHash908.result=
    (volumeState (BalanceBlindingDomain670.crypto c) w.volume.subject w.volume.dayStart w.volume.prior w.volume.priorBlinding:F) := by
  have z : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 0=1 := by
    unfold assignment
    exact RoutingParameterValues879.zero _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have cp : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial CapturedInitial73419Generic01.copy=1 := by
    unfold assignment
    exact RoutingParameterValues879.copied _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have ar : SatisfiesAt (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) CapturedFullArithmetic52.rowAt 177954 := by
    unfold assignment
    exact RoutingParameterValues879.arithmetic _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  rw [state_eq]
  exact (generic_hash _ _ _ _ _ z cp ar (VolumeHashAssignment892.subject original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (day_start original u c w legal rkInitial authInitial initial senderInitial receiverInitial) (prior original u c w legal rkInitial authInitial initial senderInitial receiverInitial) (VolumeHashAssignment892.priorBlinding original u c w legal rkInitial authInitial initial senderInitial receiverInitial)).trans
      (natural_hash c w).symm

end ShielddSecurity.VolumePriorValues909

set_option pp.all true in
#check @ShielddSecurity.VolumePriorValues909.day_start
#print axioms ShielddSecurity.VolumePriorValues909.day_start

set_option pp.all true in
#check @ShielddSecurity.VolumePriorValues909.prior
#print axioms ShielddSecurity.VolumePriorValues909.prior

set_option pp.all true in
#check @ShielddSecurity.VolumePriorValues909.starts_new_day
#print axioms ShielddSecurity.VolumePriorValues909.starts_new_day

set_option pp.all true in
#check @ShielddSecurity.VolumePriorValues909.natural_hash
#print axioms ShielddSecurity.VolumePriorValues909.natural_hash

set_option pp.all true in
#check @ShielddSecurity.VolumePriorValues909.hash_value
#print axioms ShielddSecurity.VolumePriorValues909.hash_value

set_option pp.all true in
#check @ShielddSecurity.VolumePriorValues909.generic_hash
#print axioms ShielddSecurity.VolumePriorValues909.generic_hash

set_option pp.all true in
#check @ShielddSecurity.VolumePriorValues909.state_eq
#print axioms ShielddSecurity.VolumePriorValues909.state_eq
