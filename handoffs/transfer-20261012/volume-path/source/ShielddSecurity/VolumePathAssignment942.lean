import ShielddSecurity.VolumePathBindings941
import ShielddSecurity.VolumeHashAssignment892
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePathAssignment942
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model VolumeHashAssignment892.assignment
  RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment
  RoutingPrecisionRows819.assignment SemanticCopiesRows801.assignment

def assignment (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  VolumeHashAssignment892.assignment (VolumePathSeed936.seed original w) u c w legal
    rkInitial authInitial initial senderInitial receiverInitial
attribute [local irreducible] assignment
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem frame (column : Nat) (member : column∈VolumePathLayout933.columns) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial column=VolumePathSeed936.seed original w column := by
  have bounds := VolumePathLayout933.bounds column member
  let base := VolumePathSeed936.seed original w
  have hash : VolumeHashSeed886.seed base w column=base column := by
    rw [VolumeHashSeed886.seed,if_neg (by simp only [VolumeHashLayout883.columns,List.mem_cons,List.not_mem_nil,or_false];omega)]
  have parameter := RoutingParameterSeed866.outside (VolumeHashSeed886.seed base w) w column (Or.inl (by omega))
  have candidate := VolumeCandidateSeed848.outside (RoutingParameterSeed866.seed (VolumeHashSeed886.seed base w) w) w column (by omega)
  have boundary : VolumeBoundarySeed836.seed (VolumeCandidateSeed848.seed (RoutingParameterSeed866.seed (VolumeHashSeed886.seed base w) w) w) w column=
      VolumeCandidateSeed848.seed (RoutingParameterSeed866.seed (VolumeHashSeed886.seed base w) w) w column := by
    simp only [VolumeBoundarySeed836.seed,if_neg (show column≠7739 by omega),if_neg (show column≠8255 by omega)]
  have routing := RoutingPrecisionSeed811.outside (VolumeBoundarySeed836.seed (VolumeCandidateSeed848.seed (RoutingParameterSeed866.seed (VolumeHashSeed886.seed base w) w) w) w) w column (Or.inl (by omega))
  unfold assignment VolumeHashAssignment892.assignment RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment
  exact (VolumePathBindings941.current_frame _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
    column member (by intro impossible; simp only [VolumePathLayout933.flags,List.not_mem_nil] at impossible)).trans
      (routing.trans (boundary.trans (candidate.trans (parameter.trans hash))))
theorem sibling (level : Fin 24) (slot : Fin 3) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial (8388+3*level.val+slot.val)=(w.volume.priorSiblings level slot:F) :=
  (frame original u c w legal rkInitial authInitial initial senderInitial receiverInitial _ (List.mem_range'.mpr ⟨3*level.val+slot.val,by omega,by omega⟩)).trans
    (VolumePathSeed936.sibling original w level slot)
end ShielddSecurity.VolumePathAssignment942

set_option pp.all true in
#check @ShielddSecurity.VolumePathAssignment942.frame
#print axioms ShielddSecurity.VolumePathAssignment942.frame

set_option pp.all true in
#check @ShielddSecurity.VolumePathAssignment942.sibling
#print axioms ShielddSecurity.VolumePathAssignment942.sibling
