import ShielddSecurity.UserPathComposition967
import ShielddSecurity.UserPathCapture968
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathJoin969
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 TransferSem
attribute [local irreducible] SatisfiesAt ConcreteRegistrySharedEncoding294.model PoseidonNatural192.hash Poseidon.hash6 userLeaf

theorem generic_rows {G : Type} [Field G] [CharP G p] (rho : Nat → G) (c : Crypto) (w : TransferSem.Witness)
    (sender : UserSem c w w.sender) (receiver : UserSem c w w.receiver)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (control : rho 10=(if w.regulated then 1 else 0)) (anchor : rho 5=(w.userAnchor:G))
    (senderHash : eval rho UserPathHash958C37.result=
      (root c .compliance w.sender.position (userLeaf c w.asset w.sender) w.sender.siblings:G))
    (receiverHash : eval rho UserPathHash958C54.result=
      (root c .compliance w.receiver.position (userLeaf c w.asset w.receiver) w.receiver.siblings:G)) :
    UserPathCapture968.Rows rho := by
  apply UserPathCapture968.rows
  · rw [UserPathCapture968.sender_value rho arithmetic,control,anchor,senderHash]
    cases used : w.regulated
    · simp only [Bool.false_eq_true,if_false,zero_mul]
    · have membership := (sender.2.2.2.2.2.2.2.2 used).2.2
      rw [membership]
      simp
  · rw [UserPathCapture968.receiver_value rho arithmetic,control,anchor,receiverHash]
    cases used : w.regulated
    · simp only [Bool.false_eq_true,if_false,zero_mul]
    · have membership := (receiver.2.2.2.2.2.2.2.2 used).2.2
      rw [membership]
      simp

open ConcreteJubjubField01
open VolumePathAssignment942 (assignment)
attribute [local irreducible] assignment
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem control : VolumePathAssignment942.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 10=(if w.regulated then 1 else 0) := by
  unfold VolumePathAssignment942.assignment VolumeHashAssignment892.assignment RoutingParameterAssignment872.assignment
    VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment
    SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
    OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment
    MapAssignmentValues720.assignment BalanceCombined696.assignment BalanceBlindingBindings680.assignment
    BalanceSignBindings652.assignment TierFlagBindings630.assignment TierBindings617.assignment OwnershipBindings604.assignment
    PublishedInverseSeed592.assignment PublishedPointSeed584.assignment PayloadBindings565.assignment FixedFamilyBindings551.assignment
    AuthorizationRkSeed505.assignment AuthorizationFixedSeed487.assignment AuthorizationDhSeed473.assignment
    AuthorizationTraceAssignment457.assignment IvkInverseSeed426.assignment AuthorizationSharedFrame420B.assignment
    SharedAuthorizationNonidentity413.assignment
  unfold SemanticWordFrame373.assignment
  unfold UserLifecycleWord345.assignment HighZeroCompletionFrame332.assignment SharedComparisonBlocks327.assignment
  exact SharedRegulatedValue316.control_meaning _ _ w initial
theorem rows : UserPathCapture968.Rows (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  apply generic_rows _ (BalanceBlindingDomain670.crypto c) w legal.2.1.2.1 legal.2.1.2.2.1
  · exact VolumePathValues947.arithmetic original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact control original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact UserPathInputs962.anchor original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact UserPathComposition967.sender original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact UserPathComposition967.receiver original u c w legal rkInitial authInitial initial senderInitial receiverInitial
end ShielddSecurity.UserPathJoin969

set_option pp.all true in
#check @ShielddSecurity.UserPathJoin969.generic_rows
#print axioms ShielddSecurity.UserPathJoin969.generic_rows

set_option pp.all true in
#check @ShielddSecurity.UserPathJoin969.control
#print axioms ShielddSecurity.UserPathJoin969.control

set_option pp.all true in
#check @ShielddSecurity.UserPathJoin969.rows
#print axioms ShielddSecurity.UserPathJoin969.rows
