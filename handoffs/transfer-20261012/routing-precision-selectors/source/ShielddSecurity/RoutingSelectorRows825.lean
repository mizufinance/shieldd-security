import ShielddSecurity.RoutingSelectorBindings824
import ShielddSecurity.RoutingSelectorCapture823
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RoutingSelectorRows825
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open RoutingPrecisionRows819 (assignment)
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model SatisfiesAt assignment
  SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+19406+i)) 1 ∧
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+19506+i)) 1 ∧
  ∀ index : Fin 32,RoutingSelectorAdapter822.Rows rho index.val

theorem rows (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Rows (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  let rho := assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have one : rho copy=1 := by
    simpa only [rho,assignment] using VolumeControlBindings803.copied (RoutingPrecisionSeed811.seed original w) u c w legal
      rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954 := by
    simpa only [rho,assignment] using VolumeControlBindings803.arithmetic (RoutingPrecisionSeed811.seed original w) u c w legal
      rkInitial authInitial initial senderInitial receiverInitial
  refine ⟨RoutingSelectorCapture823Sum0.satisfies rho one ?_,RoutingSelectorCapture823Sum1.satisfies rho one ?_,?_⟩
  · exact RoutingSelectorBindings824.full_sum original u c w legal rkInitial authInitial initial senderInitial receiverInitial false
  · exact RoutingSelectorBindings824.full_sum original u c w legal rkInitial authInitial initial senderInitial receiverInitial true
  · intro index
    have bounds := RoutingSelectorBindings824.bounds c w legal
    have regulated := RoutingSelectorBindings824.suffix original u c w legal rkInitial authInitial initial senderInitial receiverInitial false index.val
    have unregulated := RoutingSelectorBindings824.suffix original u c w legal rkInitial authInitial initial senderInitial receiverInitial true index.val
    change eval rho (RoutingSelectorAlgebra821.suffix 19457 index.val)=RoutingPrecisionAlgebra807.suffix w.routing.regulatedPrecision index.val at regulated
    change eval rho (RoutingSelectorAlgebra821.suffix 19523 index.val)=RoutingPrecisionAlgebra807.suffix w.routing.unregulatedPrecision index.val at unregulated
    have control := RoutingSelectorBindings824.control original u c w legal rkInitial authInitial initial senderInitial receiverInitial
    change rho 10=(if w.regulated then 1 else 0) at control
    have boolean : rho 10=0 ∨ rho 10=1 := by rw [control];cases w.regulated <;> simp
    have equations := RoutingSelectorCapture823.equations rho one arithmetic index
    rw [regulated,unregulated] at equations
    apply RoutingSelectorCapture823.rows rho index
    · exact equations.1.trans (RoutingPrecisionAlgebra807.ordered_suffix _ _ _ bounds.1 bounds.2 index.isLt)
    · dsimp only
      rw [unregulated,equations.2]
      apply RoutingSelectorAlgebra821.selection _ _ _ _ _ boolean
      · rw [RoutingPrecisionAlgebra807.suffix_value _ _ (by omega) index.isLt]
        split <;> norm_num
      · rw [RoutingPrecisionAlgebra807.suffix_value _ _ bounds.2 index.isLt]
        split <;> norm_num
end ShielddSecurity.RoutingSelectorRows825

set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorRows825.Rows
#print axioms ShielddSecurity.RoutingSelectorRows825.Rows

set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorRows825.rows
#print axioms ShielddSecurity.RoutingSelectorRows825.rows
