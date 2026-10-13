import ShielddSecurity.AuthorizationFixedDomain485
import ShielddSecurity.AuthorizationFixedFrame484
import ShielddSecurity.AuthorizationDhSeed473
import ShielddSecurity.FixedTraceAccess486
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationFixedSeed487
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def empty : GroupFixedWindows.FixedWindowWitness F :=
  ⟨false,false,Group.identityPoint,Group.identityPoint,Group.identityPoint,Group.identityPoint⟩
def trace (scalar : Nat) : List (GroupFixedWindows.FixedWindowWitness F) :=
  FixedTraceConstruction478.windows model AuthorizationFixedDomain485.represented (encodeBits 252 scalar)
def window (scalar index : Nat) : GroupFixedWindows.FixedWindowWitness F := (trace scalar)[index]?.getD empty

def seed (original : Nat → F) (scalar column : Nat) : F :=
  if 4019≤column ∧ column≤4270 then
    let output := (window scalar ((column-4019)/2)).output
    if (column-4019)%2=0 then output.x else output.y
  else original column

theorem outside (original : Nat → F) (scalar column : Nat) (out : column<4019 ∨ 4270<column) :
    seed original scalar column=original column := by
  simp only [seed,if_neg (show ¬(4019≤column ∧ column≤4270) by omega)]

theorem limb (original : Nat → F) (scalar index limb : Nat) (before : index<126) (small : limb<2) :
    seed original scalar (4019+2*index+limb)=
      if limb=0 then (window scalar index).output.x else (window scalar index).output.y := by
  have bounds : 4019≤4019+2*index+limb ∧ 4019+2*index+limb≤4270 := by omega
  have quotient : (4019+2*index+limb-4019)/2=index := by omega
  have remainder : (4019+2*index+limb-4019)%2=limb := by omega
  simp only [seed,if_pos bounds,quotient,remainder]

theorem point (original : Nat → F) (scalar index : Nat) (before : index<126) :
    VariableWindowColumns449.columnPoint (seed original scalar) (4019+2*index)=(window scalar index).output := by
  have x := limb original scalar index 0 before (by decide)
  have y := limb original scalar index 1 before (by decide)
  simp only [Nat.add_zero,if_pos rfl] at x
  simp only [if_neg (show ¬(1:Nat)=0 by decide)] at y
  cases output : (window scalar index).output with
  | mk px py =>
    simp only [output] at x y
    exact congrArg₂ Group.Point.mk x y

def assignment (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  AuthorizationDhSeed473.assignment (seed original w.auth.randomizer) (AuthorizationFixedDomain485.withGenerator c)
    w legal authInitial initial senderInitial receiverInitial

theorem completed_hint (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (column : Nat)
    (inside : 4019≤column ∧ column≤4270) :
    assignment original c w legal authInitial initial senderInitial receiverInitial column=seed original w.auth.randomizer column := by
  let prior := AuthorizationDhSeed473.seed (seed original w.auth.randomizer) (AuthorizationFixedDomain485.withGenerator c) w legal
  let traced := AuthorizationTraceSeed451.seed prior
    (AuthorizationTraceAssignment457.bases (AuthorizationFixedDomain485.withGenerator c) w legal) w.auth.ivk
  have preserved := AuthorizationFixedFrame484.completed_hint (IvkInverseSeed426.seed traced w)
    (ConcreteAuthorizationCrypto430.withOperations (AuthorizationFixedDomain485.withGenerator c)) w authInitial initial
    senderInitial receiverInitial column inside
  have ivkOutside := IvkInverseSeed426.outside traced w column (by omega)
  have traceOutside := AuthorizationTraceSeed451.outside prior
    (AuthorizationTraceAssignment457.bases (AuthorizationFixedDomain485.withGenerator c) w legal) w.auth.ivk column (Or.inr (by omega))
  have dhOutside : prior column=seed original w.auth.randomizer column := by
    simp only [prior,AuthorizationDhSeed473.seed,if_neg (show column≠3765 by omega)]
  exact preserved.trans (ivkOutside.trans (traceOutside.trans dhOutside))
end ShielddSecurity.AuthorizationFixedSeed487

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedSeed487.empty
#print axioms ShielddSecurity.AuthorizationFixedSeed487.empty

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedSeed487.trace
#print axioms ShielddSecurity.AuthorizationFixedSeed487.trace

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedSeed487.window
#print axioms ShielddSecurity.AuthorizationFixedSeed487.window

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedSeed487.seed
#print axioms ShielddSecurity.AuthorizationFixedSeed487.seed

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedSeed487.outside
#print axioms ShielddSecurity.AuthorizationFixedSeed487.outside

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedSeed487.limb
#print axioms ShielddSecurity.AuthorizationFixedSeed487.limb

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedSeed487.point
#print axioms ShielddSecurity.AuthorizationFixedSeed487.point

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedSeed487.assignment
#print axioms ShielddSecurity.AuthorizationFixedSeed487.assignment

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedSeed487.completed_hint
#print axioms ShielddSecurity.AuthorizationFixedSeed487.completed_hint
