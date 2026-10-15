-- GENERATED from maintained bounded user path composition; do not edit.
import ShielddSecurity.UserPathComposition967SB00
import ShielddSecurity.UserPathComposition967SB01
import ShielddSecurity.UserPathComposition967SB02
import ShielddSecurity.UserPathComposition967SB03
import ShielddSecurity.UserPathComposition967RB00
import ShielddSecurity.UserPathComposition967RB01
import ShielddSecurity.UserPathComposition967RB02
import ShielddSecurity.UserPathComposition967RB03
import ShielddSecurity.UserLeafMeaning963
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathComposition967
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumePathAssignment942 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model
  UserTreeMeaning965.value PoseidonNatural192.hash Poseidon.hash6 userLeaf
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem sender : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) UserPathHash958C37.result=
    (root (BalanceBlindingDomain670.crypto c) .compliance w.sender.position
      (userLeaf (BalanceBlindingDomain670.crypto c) w.asset w.sender) w.sender.siblings:F) := by
  have leaf := UserLeafMeaning963.hash21 original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have h0 := leaf.trans (congrArg (fun n : Nat => (n:F)) (UserTreeMeaning965.zero (BalanceBlindingDomain670.crypto c) w.asset w.sender).symm)
  have h1 := UserPathComposition967SB00.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h0
  have h2 := UserPathComposition967SB01.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h1
  have h3 := UserPathComposition967SB02.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h2
  have h4 := UserPathComposition967SB03.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h3
  exact h4.trans (congrArg (fun n : Nat => (n:F)) (UserTreeMeaning965.final _ w.asset w.sender))
theorem receiver : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) UserPathHash958C54.result=
    (root (BalanceBlindingDomain670.crypto c) .compliance w.receiver.position
      (userLeaf (BalanceBlindingDomain670.crypto c) w.asset w.receiver) w.receiver.siblings:F) := by
  have leaf := UserLeafMeaning963.hash38 original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have h0 := leaf.trans (congrArg (fun n : Nat => (n:F)) (UserTreeMeaning965.zero (BalanceBlindingDomain670.crypto c) w.asset w.receiver).symm)
  have h1 := UserPathComposition967RB00.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h0
  have h2 := UserPathComposition967RB01.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h1
  have h3 := UserPathComposition967RB02.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h2
  have h4 := UserPathComposition967RB03.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h3
  exact h4.trans (congrArg (fun n : Nat => (n:F)) (UserTreeMeaning965.final _ w.asset w.receiver))
end ShielddSecurity.UserPathComposition967

set_option pp.all true in
#check @ShielddSecurity.UserPathComposition967.sender
#print axioms ShielddSecurity.UserPathComposition967.sender

set_option pp.all true in
#check @ShielddSecurity.UserPathComposition967.receiver
#print axioms ShielddSecurity.UserPathComposition967.receiver
