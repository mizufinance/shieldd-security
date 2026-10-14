import ShielddSecurity.SemanticCopiesBindings799
import ShielddSecurity.SemanticCopiesCapture800
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SemanticCopiesRows801
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt
  CheckingInverseRows789.assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment
  DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment SemanticCopiesSeed798.seed

def assignment (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  CheckingInverseRows789.assignment (SemanticCopiesSeed798.seed original w) u c w legal
    rkInitial authInitial initial senderInitial receiverInitial
attribute [local irreducible] assignment

theorem rows (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SemanticCopiesCapture800.Rows (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  have firstLeft := SemanticCopiesBindings799.selected original u c w legal rkInitial authInitial initial senderInitial receiverInitial 4790 (by simp [SemanticCopiesLayout795.Inside,SemanticCopiesLayout795.values])
  have firstRight := SemanticCopiesBindings799.selected original u c w legal rkInitial authInitial initial senderInitial receiverInitial 4921 (by simp [SemanticCopiesLayout795.Inside,SemanticCopiesLayout795.values])
  have secondLeft := SemanticCopiesBindings799.selected original u c w legal rkInitial authInitial initial senderInitial receiverInitial 6195 (by simp [SemanticCopiesLayout795.Inside,SemanticCopiesLayout795.values])
  have secondRight := SemanticCopiesBindings799.selected original u c w legal rkInitial authInitial initial senderInitial receiverInitial 6325 (by simp [SemanticCopiesLayout795.Inside,SemanticCopiesLayout795.values])
  have timestampLeft := VolumeTimestampBindings791.timestamp (SemanticCopiesSeed798.seed original w) u c w legal
    rkInitial authInitial initial senderInitial receiverInitial
  have timestampRight := SemanticCopiesBindings799.selected original u c w legal rkInitial authInitial initial senderInitial receiverInitial 8541 (by simp [SemanticCopiesLayout795.Inside,SemanticCopiesLayout795.values])
  unfold assignment
  exact SemanticCopiesCapture800.rows _ (firstLeft.trans firstRight.symm) (secondLeft.trans secondRight.symm)
    (timestampLeft.trans timestampRight.symm)
end ShielddSecurity.SemanticCopiesRows801

set_option pp.all true in
#check @ShielddSecurity.SemanticCopiesRows801.assignment
#print axioms ShielddSecurity.SemanticCopiesRows801.assignment

set_option pp.all true in
#check @ShielddSecurity.SemanticCopiesRows801.rows
#print axioms ShielddSecurity.SemanticCopiesRows801.rows
