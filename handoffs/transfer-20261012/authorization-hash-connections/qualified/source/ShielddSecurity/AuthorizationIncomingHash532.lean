import ShielddSecurity.AuthorizationScalarInputs531
import ShielddSecurity.AuthorizationIncomingPorts535
import ShielddSecurity.AuthorizationAddBindings510
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationIncomingHash532
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open AuthorizationRkSeed505 (assignment)
attribute [local irreducible] assignment SemanticWordFrame373.assignment SubgroupSeedCompletion203.fieldPoint
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model PoseidonNatural192.hash Poseidon.hash6 Poseidon.hash3

theorem natural_hash (c : Crypto) (w : TransferSem.Witness) :
    ((AuthorizationFixedDomain485.crypto c).hash .incomingViewingKey
      ([w.auth.nk]++pointFields w.auth.ak):F)=
    Poseidon.hash6 (Poseidon.castParameters AuthorizationHash530C55.parameters) 16
      (([w.auth.nk]++pointFields w.auth.ak).map fun x => (x:F)) := by
  change (PoseidonNatural192.hash RegistryNatural193.small RegistryNatural193.wide representation
    .incomingViewingKey ([w.auth.nk]++pointFields w.auth.ak):F)=_
  rw [show Poseidon.castParameters AuthorizationHash530C55.parameters=(RegistryNatural193.wide : Poseidon.Parameters F 6) from rfl]
  rw [PoseidonNatural192.hash_cast]
  unfold Poseidon.hash
  rw [if_neg (by change ¬(3 ≤ 2);decide)]
  rfl

set_option pp.all true in
#check @ShielddSecurity.AuthorizationIncomingHash532.natural_hash
#print axioms ShielddSecurity.AuthorizationIncomingHash532.natural_hash

theorem inputs (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    AuthorizationHash530C55.values
      (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)=
      (([w.auth.nk]++pointFields w.auth.ak).map fun x => (x:F)) := by
  have scalar := AuthorizationScalarInputs531.rk original c w legal rkInitial authInitial initial senderInitial receiverInitial
  have point := AuthorizationAddBindings510.left original c w legal rkInitial authInitial initial senderInitial receiverInitial
  have x := congrArg Group.Point.x point
  have y := congrArg Group.Point.y point
  simp only [VariableWindowColumns449.columnPoint,AuthorizationAddDomain504.left,SubgroupSeedCompletion203.fieldPoint] at x y
  exact AuthorizationIncomingPorts535.inputs _ _ _ _ scalar.key x y

set_option pp.all true in
#check @ShielddSecurity.AuthorizationIncomingHash532.inputs
#print axioms ShielddSecurity.AuthorizationIncomingHash532.inputs

theorem meaning (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    eval (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) AuthorizationHash530C55.result=
      ((AuthorizationFixedDomain485.crypto c).hash .incomingViewingKey ([w.auth.nk]++pointFields w.auth.ak):F) := by
  have one := AuthorizationRkSeed505.zero original c w legal rkInitial authInitial initial senderInitial receiverInitial
  have copy := AuthorizationRkSeed505.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic := AuthorizationRkSeed505.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial
  have hash := AuthorizationHash530C55.hash _ one (copy.trans one.symm) arithmetic
  rw [inputs original c w legal rkInitial authInitial initial senderInitial receiverInitial] at hash
  exact hash.trans (natural_hash c w).symm

set_option pp.all true in
#check @ShielddSecurity.AuthorizationIncomingHash532.meaning
#print axioms ShielddSecurity.AuthorizationIncomingHash532.meaning

theorem reduction (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    eval (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) AuthorizationHash530C55.result=
      assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 1995+
      (TransferCore.scalarOrder:F)*assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 1994 := by
  have values := AuthorizationScalarInputs531.rk original c w legal rkInitial authInitial initial senderInitial receiverInitial
  rw [meaning original c w legal rkInitial authInitial initial senderInitial receiverInitial,values.ivk,values.quotient]
  have auth := legal.2.1.2.2.2.1
  rcases auth with ⟨_,_,_,_,scalar,_,_,_,_,_,_,_⟩
  have equality := congrArg (fun x : Nat => (x:F)) scalar.2.2.2
  simpa only [Nat.cast_add,Nat.cast_mul] using equality
set_option pp.all true in
#check @ShielddSecurity.AuthorizationIncomingHash532.reduction
#print axioms ShielddSecurity.AuthorizationIncomingHash532.reduction
end ShielddSecurity.AuthorizationIncomingHash532
