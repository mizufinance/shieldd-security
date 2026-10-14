import ShielddSecurity.VolumeBoundaryAssignment842
import ShielddSecurity.VolumeBoundaryCapture843
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeBoundaryJoin844
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model SatisfiesAt
  VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment
  SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

theorem facts (c : Crypto) (w : TransferSem.Witness) (volume : VolumeSem c w) :
    (w.volume.dayStart:F)=(2-(w.volume.context:F))*(86400*(w.volume.dayIndex:F)) ∧
    (if w.volume.useReal then (1:F) else 0)*VolumeBoundarySeed836.borrow w=0 := by
  obtain ⟨_,_,_,_,context,_,dayStart,_,_,_,_,_,realSem,_,_⟩ := volume
  constructor
  · rcases context with context|context <;>
      norm_num [dayStart,context,Nat.cast_mul]
  · cases real : w.volume.useReal
    · simp [real]
    · have valid := realSem real
      have bounded : w.volume.prior+(w.outputs 0).amount≤w.registry.dailyLimit := by
        rw [←valid.2.2.1]
        exact valid.2.2.2.1
      have notLess : ¬w.registry.dailyLimit<w.volume.prior+(w.outputs 0).amount := by omega
      simp [real,VolumeBoundarySeed836.borrow,BoundedLimbComparison119.borrow,BinaryComparison100.bit,notLess]

theorem generic_rows (rho : Nat → F) (c : Crypto) (w : TransferSem.Witness) (volume : VolumeSem c w)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (one : rho copy=1)
    (inputs : TierFlagMeaning619.Inputs rho w)
    (dayIndex : rho 7608=(w.volume.dayIndex:F))
    (dayStart : rho 7739=(w.volume.dayStart:F))
    (borrow : rho 8255=VolumeBoundarySeed836.borrow w) : VolumeBoundaryCapture843.Rows rho := by
  have day := VolumeBoundaryCapture843.day_equation rho arithmetic
  have limit := VolumeBoundaryCapture843.limit_equation rho arithmetic
  simp only [eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_mul] at day limit
  have day : rho 108480=(2*rho copy-rho 7607)*(86400*rho 7608) := by
    simpa only [copy,sub_eq_add_neg,add_comm] using day
  rw [one,inputs.context,dayIndex,mul_one] at day
  rw [inputs.useReal,borrow] at limit
  have equations := facts c w volume
  exact VolumeBoundaryCapture843.rows rho (dayStart.trans (equations.1.trans day.symm)) (limit.trans equations.2)

theorem rows (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    VolumeBoundaryCapture843.Rows (VolumeBoundaryAssignment842.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  apply generic_rows _ (BalanceBlindingDomain670.crypto c) w legal.2.1.2.2.2.2.2.2.1
  · simpa only [VolumeBoundaryAssignment842.assignment] using VolumeTransitionBindings827.arithmetic
      (VolumeBoundarySeed836.seed original w) u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · simpa only [VolumeBoundaryAssignment842.assignment] using VolumeTransitionBindings827.copied
      (VolumeBoundarySeed836.seed original w) u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · simpa only [VolumeBoundaryAssignment842.assignment] using VolumeTransitionBindings827.inputs
      (VolumeBoundarySeed836.seed original w) u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · simpa only [VolumeBoundaryAssignment842.assignment] using VolumeTransitionBindings827.words
      (VolumeBoundarySeed836.seed original w) u c w legal rkInitial authInitial initial senderInitial receiverInitial 7608 (by decide +kernel)
  · exact VolumeBoundaryAssignment842.day_start original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact VolumeBoundaryAssignment842.borrow original u c w legal rkInitial authInitial initial senderInitial receiverInitial
end ShielddSecurity.VolumeBoundaryJoin844

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundaryJoin844.facts
#print axioms ShielddSecurity.VolumeBoundaryJoin844.facts

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundaryJoin844.generic_rows
#print axioms ShielddSecurity.VolumeBoundaryJoin844.generic_rows

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundaryJoin844.rows
#print axioms ShielddSecurity.VolumeBoundaryJoin844.rows
