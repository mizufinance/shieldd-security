import ShielddSecurity.VolumeCandidateRetained851
import ShielddSecurity.BalanceBlindingBindings680
import ShielddSecurity.BalanceSignBindings652
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeCandidateBlindingFrame852
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open VolumeCandidateLayout846 (columns flags)

theorem flagged_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (column : Nat) (member : column∈columns)
    (boolean : column∈flags → original column=0 ∨ original column=1) :
    TierFlagBindings630.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial column=original column := by
  have bounds := VolumeCandidateLayout846.bounds column member
  have alternatives := VolumeCandidateLayout846.alternatives column member
  have preserved := TierFlagSeed623.outside original w column (by omega)
  unfold TierFlagBindings630.assignment
  exact (VolumeCandidateRetained851.tier_frame _ c w legal rkInitial authInitial initial senderInitial receiverInitial column member
    (by rw [preserved]; exact boolean)).trans preserved

theorem sign_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (column : Nat) (member : column∈columns)
    (boolean : column∈flags → original column=0 ∨ original column=1) :
    BalanceSignBindings652.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial column=original column := by
  have bounds := VolumeCandidateLayout846.bounds column member
  have alternatives := VolumeCandidateLayout846.alternatives column member
  have preserved := BalanceSignBindings652.outside original w column (by omega)
  unfold BalanceSignBindings652.assignment
  exact (flagged_frame _ c w legal rkInitial authInitial initial senderInitial receiverInitial column member
    (by rw [preserved]; exact boolean)).trans preserved

theorem blinding_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (column : Nat) (member : column∈columns)
    (boolean : column∈flags → original column=0 ∨ original column=1) :
    BalanceBlindingBindings680.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial column=original column := by
  have bounds := VolumeCandidateLayout846.bounds column member
  have alternatives := VolumeCandidateLayout846.alternatives column member
  have preserved := BalanceBlindingTrace675.outside original w.blinding column (by omega)
  unfold BalanceBlindingBindings680.assignment
  exact (sign_frame _ (BalanceBlindingDomain670.withBlinding c) w legal rkInitial authInitial initial senderInitial receiverInitial column member
    (by rw [preserved]; exact boolean)).trans preserved
end ShielddSecurity.VolumeCandidateBlindingFrame852

set_option pp.all true in
#check @ShielddSecurity.VolumeCandidateBlindingFrame852.flagged_frame
#print axioms ShielddSecurity.VolumeCandidateBlindingFrame852.flagged_frame

set_option pp.all true in
#check @ShielddSecurity.VolumeCandidateBlindingFrame852.sign_frame
#print axioms ShielddSecurity.VolumeCandidateBlindingFrame852.sign_frame

set_option pp.all true in
#check @ShielddSecurity.VolumeCandidateBlindingFrame852.blinding_frame
#print axioms ShielddSecurity.VolumeCandidateBlindingFrame852.blinding_frame
