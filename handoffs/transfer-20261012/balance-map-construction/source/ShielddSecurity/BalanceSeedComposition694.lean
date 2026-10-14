import ShielddSecurity.BalanceMagnitudeBindings663
import ShielddSecurity.BalanceBlindingBindings680
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceSeedComposition694
open ConcretePointTorsion01 ConcreteJubjubField01 TransferSem

theorem seeds_commute (original : Nat → F) (base : curve.Point) (magnitude blinding : Nat) :
    BalanceMagnitudeTrace640.seed (BalanceBlindingTrace675.seed original blinding) base magnitude =
      BalanceBlindingTrace675.seed (BalanceMagnitudeTrace640.seed original base magnitude) blinding := by
  funext column
  by_cases magnitudeRange : 21842≤column ∧ column<22232
  · have separate : ¬(22484≤column ∧ column≤22735) := by omega
    simp only [BalanceMagnitudeTrace640.seed,BalanceBlindingTrace675.seed,
      if_pos magnitudeRange,if_neg separate]
  · by_cases blindingRange : 22484≤column ∧ column≤22735
    · simp only [BalanceMagnitudeTrace640.seed,BalanceBlindingTrace675.seed,
        if_neg magnitudeRange,if_pos blindingRange]
    · simp only [BalanceMagnitudeTrace640.seed,BalanceBlindingTrace675.seed,
        if_neg magnitudeRange,if_neg blindingRange]

theorem assignments_agree (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w) (base : curve.Point)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    BalanceBlindingBindings680.assignment
      (BalanceMagnitudeTrace640.seed original base (RemainingWordSeed369.magnitude w))
      c w legal rkInitial authInitial initial senderInitial receiverInitial =
    BalanceMagnitudeBindings663.assignment (BalanceBlindingTrace675.seed original w.blinding)
      (BalanceBlindingDomain670.withBlinding c) w legal base
      rkInitial authInitial initial senderInitial receiverInitial := by
  unfold BalanceBlindingBindings680.assignment BalanceMagnitudeBindings663.assignment
  rw [seeds_commute]
end ShielddSecurity.BalanceSeedComposition694

set_option pp.all true in
#check @ShielddSecurity.BalanceSeedComposition694.seeds_commute
#print axioms ShielddSecurity.BalanceSeedComposition694.seeds_commute

set_option pp.all true in
#check @ShielddSecurity.BalanceSeedComposition694.assignments_agree
#print axioms ShielddSecurity.BalanceSeedComposition694.assignments_agree
