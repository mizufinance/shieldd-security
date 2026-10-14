import ShielddSecurity.SemanticCopiesFrame797
import ShielddSecurity.SemanticCopiesSeed798
import ShielddSecurity.VolumeTimestampBindings791
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SemanticCopiesBindings799
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open CheckingInverseRows789 (assignment)
attribute [local irreducible] model assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment
  DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

theorem original (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (column : Nat)
    (inside : SemanticCopiesLayout795.Inside column) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial column=original column := by
  have bounds := SemanticCopiesLayout795.bounds column inside
  have alternatives := SemanticCopiesLayout795.alternatives column inside
  unfold assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment DetectionNonidentityRows765.assignment
    BalanceFinalRows753.assignment MapAssignmentValues720.assignment BalanceCombined696.assignment
  rw [SemanticCopiesFrame797.blinding_frame _ c w legal rkInitial authInitial initial senderInitial receiverInitial column inside,
    BalanceMagnitudeTrace640.outside _ _ _ column (Or.inl (by omega)),
    BalanceMapSeed703.outside _ u column (by
      simp only [BalanceMapSeed703.columns,List.mem_cons,List.not_mem_nil,or_false];omega)]
  simp only [BalanceFinalDomain751.seed,DetectionNonidentityDomain759.seed,OutputAmountDomain767.seed,RecoveryInverseSeed778.seed,
    CheckingInverseSeed783.seed,
    if_neg (show column≠22736 by omega),if_neg (show column≠1503 by omega),if_neg (show column≠4919 by omega),
    if_neg (show column≠6192 by omega),if_neg (show column≠7596 by omega),
    if_neg (show column≠9057 by omega),if_neg (show column≠10589 by omega)]

theorem selected (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (column : Nat)
    (inside : SemanticCopiesLayout795.Inside column) :
    assignment (SemanticCopiesSeed798.seed original w) u c w legal rkInitial authInitial initial senderInitial receiverInitial column=
      SemanticCopiesSeed798.value w column :=
  (SemanticCopiesBindings799.original _ u c w legal rkInitial authInitial initial senderInitial receiverInitial column inside).trans
    (SemanticCopiesSeed798.selected original w column inside)
end ShielddSecurity.SemanticCopiesBindings799

set_option pp.all true in
#check @ShielddSecurity.SemanticCopiesBindings799.original
#print axioms ShielddSecurity.SemanticCopiesBindings799.original

set_option pp.all true in
#check @ShielddSecurity.SemanticCopiesBindings799.selected
#print axioms ShielddSecurity.SemanticCopiesBindings799.selected
