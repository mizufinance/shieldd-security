import ShielddSecurity.BalanceSeedComposition694
import ShielddSecurity.BalanceMagnitudeAggregate695
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceCombined696
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
attribute [local irreducible] model

noncomputable def assignment (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w) (base : curve.Point)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  BalanceBlindingBindings680.assignment
    (BalanceMagnitudeTrace640.seed original base (RemainingWordSeed369.magnitude w)) c w legal
    rkInitial authInitial initial senderInitial receiverInitial
attribute [local irreducible] assignment

-- The base correspondence is deliberately retained as a premise.
theorem magnitude_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w) (base : curve.Point)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (baseMeaning : VariableWindowJoin443.point (assignment original c w legal base rkInitial authInitial initial senderInitial receiverInitial)
      [(190237,1)] [(190241,1)]=model.coordinates base) :
    CompilerAssertionBlock51.SatisfiesAt (assignment original c w legal base rkInitial authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+21914+i)) 390 := by
  unfold assignment at baseMeaning ⊢
  rw [BalanceSeedComposition694.assignments_agree] at baseMeaning ⊢
  exact BalanceMagnitudeAggregate695.all_rows _ (BalanceBlindingDomain670.withBlinding c) w legal base
    rkInitial authInitial initial senderInitial receiverInitial baseMeaning

theorem magnitude_bound (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w) :
    RemainingWordSeed369.magnitude w<2^129 := by
  exact RemainingWordSeed369.value_bound
    (ConcreteAuthorizationCrypto430.withOperations (AuthorizationFixedDomain485.withGenerator
      (DetectionGroupDomain611.baseCrypto (BalanceBlindingDomain670.withBlinding c)))) w legal
    21712 (by decide +kernel)

theorem magnitude_final_point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w) (base : curve.Point)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    VariableWindowColumns449.columnPoint (assignment original c w legal base rkInitial authInitial initial senderInitial receiverInitial) 22230=
      model.coordinates (RemainingWordSeed369.magnitude w • base) := by
  unfold assignment
  rw [BalanceSeedComposition694.assignments_agree]
  have point := BalanceMagnitudeBindings663.point (BalanceBlindingTrace675.seed original w.blinding)
    (BalanceBlindingDomain670.withBlinding c) w legal base rkInitial authInitial initial
    senderInitial receiverInitial 194 (by decide)
  change VariableWindowColumns449.columnPoint
    (BalanceMagnitudeBindings663.assignment (BalanceBlindingTrace675.seed original w.blinding)
      (BalanceBlindingDomain670.withBlinding c) w legal base rkInitial authInitial initial
      senderInitial receiverInitial) 22230=
      (BalanceMagnitudeTrace640.windowAt base (RemainingWordSeed369.magnitude w) 64).output at point
  exact point.trans (BalanceMagnitudeTrace640.last_output base _ (magnitude_bound c w legal))
end ShielddSecurity.BalanceCombined696

set_option pp.all true in
#check @ShielddSecurity.BalanceCombined696.magnitude_rows
#print axioms ShielddSecurity.BalanceCombined696.magnitude_rows

set_option pp.all true in
#check @ShielddSecurity.BalanceCombined696.magnitude_bound
#print axioms ShielddSecurity.BalanceCombined696.magnitude_bound

set_option pp.all true in
#check @ShielddSecurity.BalanceCombined696.magnitude_final_point
#print axioms ShielddSecurity.BalanceCombined696.magnitude_final_point
