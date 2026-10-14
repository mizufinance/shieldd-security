import ShielddSecurity.RoutingPrecisionBlindingFrame815
import ShielddSecurity.SemanticCopiesRows801
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RoutingPrecisionBindings816
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open RoutingPrecisionLayout808 (columns flags)
attribute [local irreducible] model MapAssignmentValues720.assignment BalanceFinalRows753.assignment
  DetectionNonidentityRows765.assignment OutputAmountRows773.assignment RecoveryInverseRows781.assignment
  CheckingInverseRows789.assignment SemanticCopiesRows801.assignment

variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (column : Nat) (member : column∈columns)
    (boolean : column∈flags → original column=0 ∨ original column=1)

include member boolean

theorem magnitude_frame :
    BalanceCombined696.assignment original c w legal (BalanceMapPoint701.represented u)
      rkInitial authInitial initial senderInitial receiverInitial column=original column := by
  have bounds := RoutingPrecisionLayout808.bounds column member
  have preserved := BalanceMagnitudeTrace640.outside original (BalanceMapPoint701.represented u)
    (RemainingWordSeed369.magnitude w) column (by omega)
  unfold BalanceCombined696.assignment
  exact (RoutingPrecisionBlindingFrame815.blinding_frame _ c w legal rkInitial authInitial initial senderInitial receiverInitial
    column member (by rw [preserved]; exact boolean)).trans preserved

theorem map_frame :
    MapAssignmentValues720.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial column=original column := by
  have bounds := RoutingPrecisionLayout808.bounds column member
  have preserved := BalanceMapSeed703.outside original u column (by
    simp only [BalanceMapSeed703.columns,List.mem_cons,List.not_mem_nil,or_false];omega)
  unfold MapAssignmentValues720.assignment
  exact (magnitude_frame _ u c w legal rkInitial authInitial initial senderInitial receiverInitial column member
    (by rw [preserved]; exact boolean)).trans preserved

theorem final_frame :
    BalanceFinalRows753.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial column=original column := by
  have bounds := RoutingPrecisionLayout808.bounds column member
  have preserved : BalanceFinalDomain751.seed original u w column=original column := by
    simp only [BalanceFinalDomain751.seed,if_neg (show column≠22736 by omega)]
  unfold BalanceFinalRows753.assignment
  exact (map_frame _ u c w legal rkInitial authInitial initial senderInitial receiverInitial column member
    (by rw [preserved]; exact boolean)).trans preserved

theorem detection_frame :
    DetectionNonidentityRows765.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial column=original column := by
  have bounds := RoutingPrecisionLayout808.bounds column member
  have preserved : DetectionNonidentityDomain759.seed original (BalanceBlindingDomain670.withBlinding c) w column=original column := by
    simp only [DetectionNonidentityDomain759.seed,if_neg (show column≠1503 by omega)]
  unfold DetectionNonidentityRows765.assignment
  exact (final_frame _ u c w legal rkInitial authInitial initial senderInitial receiverInitial column member
    (by rw [preserved]; exact boolean)).trans preserved

theorem amount_frame :
    OutputAmountRows773.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial column=original column := by
  have bounds := RoutingPrecisionLayout808.bounds column member
  have preserved : OutputAmountDomain767.seed original w column=original column := by
    simp only [OutputAmountDomain767.seed,if_neg (show column≠4919 by omega)]
  unfold OutputAmountRows773.assignment
  exact (detection_frame _ u c w legal rkInitial authInitial initial senderInitial receiverInitial column member
    (by rw [preserved]; exact boolean)).trans preserved

theorem recovery_frame :
    RecoveryInverseRows781.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial column=original column := by
  have bounds := RoutingPrecisionLayout808.bounds column member
  have preserved := RecoveryInverseSeed778.outside original w column (by omega) (by omega)
  unfold RecoveryInverseRows781.assignment
  exact (amount_frame _ u c w legal rkInitial authInitial initial senderInitial receiverInitial column member
    (by rw [preserved]; exact boolean)).trans preserved

theorem checking_frame :
    CheckingInverseRows789.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial column=original column := by
  have bounds := RoutingPrecisionLayout808.bounds column member
  have preserved := CheckingInverseSeed783.outside original (DetectionGroupDomain611.baseCrypto (BalanceBlindingDomain670.withBlinding c)) w column (by omega) (by omega)
  unfold CheckingInverseRows789.assignment
  exact (recovery_frame _ u c w legal rkInitial authInitial initial senderInitial receiverInitial column member
    (by rw [preserved]; exact boolean)).trans preserved

theorem current_frame :
    SemanticCopiesRows801.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial column=original column := by
  have bounds := RoutingPrecisionLayout808.bounds column member
  have preserved := SemanticCopiesSeed798.outside original w column (by
    intro inside
    have earlier := SemanticCopiesLayout795.bounds column inside
    omega)
  unfold SemanticCopiesRows801.assignment
  exact (checking_frame _ u c w legal rkInitial authInitial initial senderInitial receiverInitial column member
    (by rw [preserved]; exact boolean)).trans preserved

omit boolean in
theorem seeded_frame :
    SemanticCopiesRows801.assignment (RoutingPrecisionSeed811.seed original w) u c w legal
      rkInitial authInitial initial senderInitial receiverInitial column=RoutingPrecisionSeed811.seed original w column :=
  current_frame _ u c w legal rkInitial authInitial initial senderInitial receiverInitial column member
    (RoutingPrecisionSeed811.boolean original w column)
end ShielddSecurity.RoutingPrecisionBindings816

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionBindings816.magnitude_frame
#print axioms ShielddSecurity.RoutingPrecisionBindings816.magnitude_frame

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionBindings816.map_frame
#print axioms ShielddSecurity.RoutingPrecisionBindings816.map_frame

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionBindings816.final_frame
#print axioms ShielddSecurity.RoutingPrecisionBindings816.final_frame

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionBindings816.detection_frame
#print axioms ShielddSecurity.RoutingPrecisionBindings816.detection_frame

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionBindings816.amount_frame
#print axioms ShielddSecurity.RoutingPrecisionBindings816.amount_frame

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionBindings816.recovery_frame
#print axioms ShielddSecurity.RoutingPrecisionBindings816.recovery_frame

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionBindings816.checking_frame
#print axioms ShielddSecurity.RoutingPrecisionBindings816.checking_frame

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionBindings816.current_frame
#print axioms ShielddSecurity.RoutingPrecisionBindings816.current_frame

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionBindings816.seeded_frame
#print axioms ShielddSecurity.RoutingPrecisionBindings816.seeded_frame
