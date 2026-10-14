import ShielddSecurity.BalanceSignBindings652
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceWordValues653
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

theorem values (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (column : Nat) (member : column∈RemainingWordSeed369.values) :
    BalanceSignBindings652.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial column=
      (RemainingWordSeed369.value w column:F) := by
  unfold BalanceSignBindings652.assignment TierFlagBindings630.assignment TierBindings617.assignment
    OwnershipBindings604.assignment PublishedInverseSeed592.assignment PublishedPointSeed584.assignment
    PayloadBindings565.assignment FixedFamilyBindings551.assignment AuthorizationRkSeed505.assignment
    AuthorizationFixedSeed487.assignment AuthorizationDhSeed473.assignment AuthorizationTraceAssignment457.assignment
    IvkInverseSeed426.assignment AuthorizationSharedFrame420B.assignment SharedAuthorizationNonidentity413.assignment
  exact SemanticWordFrame373.remaining_value _ _ w initial senderInitial receiverInitial column member
end ShielddSecurity.BalanceWordValues653
set_option pp.all true in
#check @ShielddSecurity.BalanceWordValues653.values
#print axioms ShielddSecurity.BalanceWordValues653.values
