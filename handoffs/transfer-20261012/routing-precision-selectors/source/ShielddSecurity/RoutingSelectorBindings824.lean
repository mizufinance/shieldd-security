import ShielddSecurity.RoutingPrecisionRows819
import ShielddSecurity.RoutingSelectorAlgebra821
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RoutingSelectorBindings824
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open RoutingPrecisionRows819 (assignment)
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model SatisfiesAt assignment
  SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

theorem base_control (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    AuthorizationRkSeed505.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 10=
      (if w.regulated then 1 else 0) := by
  unfold AuthorizationRkSeed505.assignment AuthorizationFixedSeed487.assignment AuthorizationDhSeed473.assignment
    AuthorizationTraceAssignment457.assignment IvkInverseSeed426.assignment AuthorizationSharedFrame420B.assignment
    SharedAuthorizationNonidentity413.assignment SemanticWordFrame373.assignment UserLifecycleWord345.assignment
    HighZeroCompletionFrame332.assignment SharedComparisonBlocks327.assignment
  exact SharedRegulatedValue316.control_meaning _ _ w initial

variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)

include legal in
theorem bounds : w.routing.regulatedPrecision≤w.routing.unregulatedPrecision ∧ w.routing.unregulatedPrecision≤32 := by
  obtain ⟨_,_,_,_,_,_,_,routing,_,_⟩ := legal.2.1
  exact ⟨routing.1,routing.2.1⟩

theorem control : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 10=
    (if w.regulated then 1 else 0) := by
  unfold assignment SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
    OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment
    MapAssignmentValues720.assignment BalanceCombined696.assignment BalanceBlindingBindings680.assignment
    BalanceSignBindings652.assignment TierFlagBindings630.assignment TierBindings617.assignment OwnershipBindings604.assignment
    PublishedInverseSeed592.assignment PublishedPointSeed584.assignment PayloadBindings565.assignment FixedFamilyBindings551.assignment
  exact base_control _ _ w legal rkInitial authInitial initial senderInitial receiverInitial

theorem flag (family : Bool) (index : Nat) (before : index<33) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial (RoutingPrecisionSeed811.start family+2*index)=
      FieldZeroSeed125.flag ((RoutingPrecisionSeed811.precision w family:F)-(index:F)) := by
  rw [RoutingPrecisionRows819.frame original u c w legal rkInitial authInitial initial senderInitial receiverInitial _
    (RoutingPrecisionRows819.column_member _ (by cases family <;> simp only [RoutingPrecisionSeed811.start,if_true,Bool.false_eq_true,if_false] <;> omega)
      (by cases family <;> simp only [RoutingPrecisionSeed811.start,if_true,Bool.false_eq_true,if_false] <;> omega))]
  exact RoutingPrecisionSeed811.flag original w family ⟨index,before⟩

theorem full_sum (family : Bool) :
    eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (RoutingSelectorAlgebra821.flags (RoutingPrecisionSeed811.start family) (List.range 33))=1 := by
  apply RoutingSelectorAlgebra821.full_sum _ (RoutingPrecisionSeed811.precision w family)
  · have legalBounds := bounds c w legal
    cases family <;> simp only [RoutingPrecisionSeed811.precision,if_true,Bool.false_eq_true,if_false] <;> omega
  · exact flag original u c w legal rkInitial authInitial initial senderInitial receiverInitial family

theorem suffix (family : Bool) (index : Nat) :
    eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (RoutingSelectorAlgebra821.suffix (RoutingPrecisionSeed811.start family) index)=
      RoutingPrecisionAlgebra807.suffix (RoutingPrecisionSeed811.precision w family) index :=
  RoutingSelectorAlgebra821.suffix_value _ _ _ _
    (flag original u c w legal rkInitial authInitial initial senderInitial receiverInitial family)
end ShielddSecurity.RoutingSelectorBindings824

set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorBindings824.base_control
#print axioms ShielddSecurity.RoutingSelectorBindings824.base_control

set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorBindings824.bounds
#print axioms ShielddSecurity.RoutingSelectorBindings824.bounds

set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorBindings824.control
#print axioms ShielddSecurity.RoutingSelectorBindings824.control

set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorBindings824.flag
#print axioms ShielddSecurity.RoutingSelectorBindings824.flag

set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorBindings824.full_sum
#print axioms ShielddSecurity.RoutingSelectorBindings824.full_sum

set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorBindings824.suffix
#print axioms ShielddSecurity.RoutingSelectorBindings824.suffix
