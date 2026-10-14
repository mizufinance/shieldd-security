import ShielddSecurity.RoutingParameterValues879
import ShielddSecurity.RoutingParameterCapture880
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RoutingParameterJoin881
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open RoutingParameterAssignment872 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model SatisfiesAt Poseidon.hash6
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem hash_value : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) RoutingParameterHash878.result=
    ((BalanceBlindingDomain670.crypto c).hash .routeParameters
      [w.routing.regulatedPrecision,w.routing.unregulatedPrecision,w.routing.height]:F) := by
  have zero := RoutingParameterValues879.zero original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have copied := RoutingParameterValues879.copied original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic := RoutingParameterValues879.arithmetic original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have result := RoutingParameterHash878.hash _ zero (copied.trans zero.symm) arithmetic
  rw [RoutingParameterValues879.regulated original u c w legal rkInitial authInitial initial senderInitial receiverInitial,RoutingParameterValues879.unregulated original u c w legal rkInitial authInitial initial senderInitial receiverInitial,
    RoutingParameterAssignment872.height original u c w legal rkInitial authInitial initial senderInitial receiverInitial] at result
  exact result.trans (RoutingParameterValues879.natural_hash c w).symm

theorem rows : RoutingParameterCapture880.Rows (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  apply RoutingParameterCapture880.rows
  rw [hash_value original u c w legal rkInitial authInitial initial senderInitial receiverInitial,RoutingParameterAssignment872.parameter_set original u c w legal rkInitial authInitial initial senderInitial receiverInitial]
  obtain ⟨_,_,_,_,_,_,_,routing,_,_⟩ := legal.2.1
  exact congrArg (fun n : Nat => (n:F)) routing.2.2.1.symm
end ShielddSecurity.RoutingParameterJoin881

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterJoin881.hash_value
#print axioms ShielddSecurity.RoutingParameterJoin881.hash_value

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterJoin881.rows
#print axioms ShielddSecurity.RoutingParameterJoin881.rows
