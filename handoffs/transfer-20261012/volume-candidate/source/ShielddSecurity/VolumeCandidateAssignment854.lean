import ShielddSecurity.VolumeCandidateBindings853
import ShielddSecurity.VolumeBoundaryAssignment842
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeCandidateAssignment854
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment
  SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

def assignment (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  VolumeBoundaryAssignment842.assignment (VolumeCandidateSeed848.seed original w) u c w legal
    rkInitial authInitial initial senderInitial receiverInitial
attribute [local irreducible] assignment

variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)

theorem frame (column : Nat) (member : column∈VolumeCandidateLayout846.columns) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial column=
      VolumeCandidateSeed848.seed original w column := by
  have bounds := VolumeCandidateLayout846.bounds column member
  have boundary : VolumeBoundarySeed836.seed (VolumeCandidateSeed848.seed original w) w column=VolumeCandidateSeed848.seed original w column := by
    simp only [VolumeBoundarySeed836.seed,if_neg (show column≠7739 by omega),if_neg (show column≠8255 by omega)]
  have routing := RoutingPrecisionSeed811.outside (VolumeBoundarySeed836.seed (VolumeCandidateSeed848.seed original w) w) w column (Or.inl (by omega))
  unfold assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment
  exact (VolumeCandidateBindings853.current_frame _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
    column member (by rw [routing,boundary];exact VolumeCandidateSeed848.boolean original w column)).trans (routing.trans boundary)

theorem bits (index : Nat) (bound : index<128) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial (8127+index)=
      BooleanHints207.bitValue (VolumeCandidateSeed848.flag w index) := by
  have member : 8127+index∈VolumeCandidateLayout846.columns :=
    List.mem_range'.mpr ⟨index,bound,by simp⟩
  exact (frame original u c w legal rkInitial authInitial initial senderInitial receiverInitial _ member).trans
    (VolumeCandidateSeed848.selected original w index bound)
end ShielddSecurity.VolumeCandidateAssignment854

set_option pp.all true in
#check @ShielddSecurity.VolumeCandidateAssignment854.frame
#print axioms ShielddSecurity.VolumeCandidateAssignment854.frame

set_option pp.all true in
#check @ShielddSecurity.VolumeCandidateAssignment854.bits
#print axioms ShielddSecurity.VolumeCandidateAssignment854.bits
