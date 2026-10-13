import ShielddSecurity.AuthorizationRkBindings507
import ShielddSecurity.AuthorizationAddBindings510
import ShielddSecurity.AuthorizationRandomizerBindings515
import ShielddSecurity.AuthorizationAddRows511
import ShielddSecurity.RkInverseRows513
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationRkConstruction512
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open AuthorizationRkSeed505 (assignment seed)
attribute [local irreducible] SemanticWordFrame373.assignment SubgroupSeedCompletion203.fieldPoint assignment

theorem nonidentity_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    CapturedRkInverse508.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  have x := AuthorizationRkSeed505.completed_value original c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨0,by decide⟩
  exact RkInverseRows513.rows _ (w.auth.rk.x:F)
    (AuthorizationRkSeed505.zero original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (AuthorizationRkSeed505.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (AuthorizationRkSeed505.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial) x
    (AuthorizationRkBindings507.inverse original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (AuthorizationRkDomain503.x_nonzero (ConcreteAuthorizationCrypto430.withOperations (AuthorizationFixedDomain485.withGenerator c)) w legal)

theorem addition_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    CapturedAuthorizationAdd509.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  exact AuthorizationAddRows511.complete _
    (AuthorizationRkSeed505.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (AuthorizationRkSeed505.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (AuthorizationAddDomain504.left w) (AuthorizationAddDomain504.right w) (SubgroupSeedCompletion203.fieldPoint w.auth.rk)
    (AuthorizationAddBindings510.left original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (AuthorizationRandomizerBindings515.right original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (AuthorizationRkBindings507.point original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (AuthorizationRkSeed505.completed_inverse original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (AuthorizationAddDomain504.denominator_nonzero c w legal) (AuthorizationAddDomain504.result c w legal).symm

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  AuthorizationFixedBindings492.Earlier (seed original w rkInitial) c w legal authInitial initial senderInitial receiverInitial ∧
  AuthorizationFixedConstruction497.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) ∧
  SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (fun i => CapturedFullRelation58.rowAt (177954+4028+i)) 2

def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+4281+i)) 6 ∧
  CapturedRkInverse508.Rows rho ∧ CapturedAuthorizationAdd509.Rows rho

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,valid,binding⟩ := AuthorizationRkDomain503.preimage
    (ConcreteAuthorizationCrypto430.withOperations (AuthorizationFixedDomain485.withGenerator c)) w legal
  obtain ⟨authInitial,senderInitial,receiverInitial,initial,earlier,ordinary,first⟩ :=
    AuthorizationFixedInitial499.legal_completed (seed original w rkInitial) c w legal
  have retained : Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial := by
    unfold Earlier assignment
    exact ⟨earlier,ordinary,first⟩
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,retained,
    AuthorizationRkBindings507.subgroup_rows original c w legal rkInitial authInitial initial senderInitial receiverInitial valid binding,
    nonidentity_rows original c w legal rkInitial authInitial initial senderInitial receiverInitial,
    addition_rows original c w legal rkInitial authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.AuthorizationRkConstruction512

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkConstruction512.nonidentity_rows
#print axioms ShielddSecurity.AuthorizationRkConstruction512.nonidentity_rows

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkConstruction512.addition_rows
#print axioms ShielddSecurity.AuthorizationRkConstruction512.addition_rows

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkConstruction512.Earlier
#print axioms ShielddSecurity.AuthorizationRkConstruction512.Earlier

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkConstruction512.Rows
#print axioms ShielddSecurity.AuthorizationRkConstruction512.Rows

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkConstruction512.legal_completed
#print axioms ShielddSecurity.AuthorizationRkConstruction512.legal_completed
