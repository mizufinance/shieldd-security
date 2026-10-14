import ShielddSecurity.RoutingParameterAssignment872
import ShielddSecurity.RoutingParameterHash878
import ShielddSecurity.VolumeTransitionBindings827
import ShielddSecurity.MapInverseRows722
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RoutingParameterValues879
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open RoutingParameterAssignment872 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model SatisfiesAt PoseidonNatural192.hash Poseidon.hash6
  VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment
  SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem regulated : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 19455=(w.routing.regulatedPrecision:F) := by
  unfold assignment VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment
  exact RoutingPrecisionRows819.input _ u c w legal rkInitial authInitial initial senderInitial receiverInitial 0
theorem unregulated : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 19456=(w.routing.unregulatedPrecision:F) := by
  unfold assignment VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment
  exact RoutingPrecisionRows819.input _ u c w legal rkInitial authInitial initial senderInitial receiverInitial 33
theorem arithmetic : SatisfiesAt (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) CapturedFullArithmetic52.rowAt 177954 := by
  unfold assignment VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment
  exact VolumeTransitionBindings827.arithmetic _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
theorem copied : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial CapturedInitial73419Generic01.copy=1 := by
  unfold assignment VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment
  exact VolumeTransitionBindings827.copied _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
theorem zero : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 0=1 := by
  unfold assignment VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment SemanticCopiesRows801.assignment CheckingInverseRows789.assignment
    RecoveryInverseRows781.assignment OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment
  exact MapInverseRows722.zero _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
theorem natural_hash (c : Crypto) (w : TransferSem.Witness) :
    ((BalanceBlindingDomain670.crypto c).hash .routeParameters
      [w.routing.regulatedPrecision,w.routing.unregulatedPrecision,w.routing.height]:F)=
    Poseidon.hash6 (Poseidon.castParameters RoutingParameterHash878.parameters) 33
      [(w.routing.regulatedPrecision:F),(w.routing.unregulatedPrecision:F),(w.routing.height:F)] := by
  change (PoseidonNatural192.hash RegistryNatural193.small RegistryNatural193.wide ConcreteRegistrySharedEncoding294.representation
    .routeParameters [w.routing.regulatedPrecision,w.routing.unregulatedPrecision,w.routing.height]:F)=_
  rw [show Poseidon.castParameters RoutingParameterHash878.parameters=(RegistryNatural193.wide : Poseidon.Parameters F 6) from rfl]
  rw [PoseidonNatural192.hash_cast]
  unfold Poseidon.hash
  rw [if_neg (by change ¬3≤2;decide)]
  rfl
end ShielddSecurity.RoutingParameterValues879

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterValues879.regulated
#print axioms ShielddSecurity.RoutingParameterValues879.regulated

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterValues879.unregulated
#print axioms ShielddSecurity.RoutingParameterValues879.unregulated

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterValues879.arithmetic
#print axioms ShielddSecurity.RoutingParameterValues879.arithmetic

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterValues879.copied
#print axioms ShielddSecurity.RoutingParameterValues879.copied

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterValues879.zero
#print axioms ShielddSecurity.RoutingParameterValues879.zero

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterValues879.natural_hash
#print axioms ShielddSecurity.RoutingParameterValues879.natural_hash
