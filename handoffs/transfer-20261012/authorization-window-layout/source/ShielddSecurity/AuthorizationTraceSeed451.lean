import ShielddSecurity.AuthorizationGroupDomain445
import ShielddSecurity.AuthorizationTraceIndex450
import ShielddSecurity.VariableWindowColumns449
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationTraceSeed451
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open TransferSem AuthorizationTraceIndex450

def empty : TransferOwnership.WindowWitness F :=
  ⟨false,false,Group.identityPoint,Group.identityPoint,Group.identityPoint⟩
def trace (base : curve.Point) (scalar : Nat) : List (TransferOwnership.WindowWitness F) :=
  VariableTraceBits446.windows model base (encodeBits 252 scalar)
def windowAt (base : curve.Point) (scalar window : Nat) : TransferOwnership.WindowWitness F :=
  (trace base scalar)[window]?.getD empty
def component (value : TransferOwnership.WindowWitness F) (index : Nat) : Group.Point F :=
  if index=0 then value.first else if index=1 then value.second else value.output
def hintPoint (base : curve.Point) (scalar index : Nat) : Group.Point F :=
  if index=0 then model.coordinates (2 • base)
  else if index=1 then model.coordinates (3 • base)
  else if index=2 then (windowAt base scalar 0).output
  else component (windowAt base scalar ((index-3)/3+1)) ((index-3)%3)
def coordinate (point : Group.Point F) (limb : Nat) : F := if limb=0 then point.x else point.y

def seed (original : Nat → F) (bases : Nat → curve.Point) (scalar column : Nat) : F :=
  if 2253≤column ∧ column≤3764 then
    coordinate (hintPoint (bases ((column-2253)/756)) scalar (((column-2253)%756)/2)) ((column-2253)%2)
  else original column

theorem outside (original : Nat → F) (bases : Nat → curve.Point) (scalar column : Nat)
    (outside : column<2253 ∨ 3764<column) : seed original bases scalar column=original column := by
  have out : ¬ (2253≤column ∧ column≤3764) := by omega
  simp only [seed,if_neg out]

theorem window_limb (original : Nat → F) (bases : Nat → curve.Point) (scalar family window part limb : Nat)
    (familyBound : family<2) (windowLower : 1≤window) (windowBound : window<126)
    (partBound : part<3) (limbBound : limb<2) :
    seed original bases scalar (column family window part limb)=
      coordinate (component (windowAt (bases family) scalar window) part) limb := by
  obtain ⟨lower,upper,familyEqual,pointEqual,limbEqual,pointLower,windowEqual,partEqual⟩ :=
    window_decode family window part limb familyBound windowLower windowBound partBound limbBound
  rw [seed,if_pos ⟨lower,upper⟩,familyEqual,pointEqual,limbEqual]
  simp only [hintPoint,if_neg (show 3*window+part≠0 by omega),
    if_neg (show 3*window+part≠1 by omega),if_neg (show 3*window+part≠2 by omega),windowEqual,partEqual]

theorem window_point (original : Nat → F) (bases : Nat → curve.Point) (scalar family window part : Nat)
    (familyBound : family<2) (windowLower : 1≤window) (windowBound : window<126) (partBound : part<3) :
    VariableWindowColumns449.columnPoint (seed original bases scalar) (column family window part 0)=
      component (windowAt (bases family) scalar window) part := by
  change Group.Point.mk (seed original bases scalar (column family window part 0))
    (seed original bases scalar (column family window part 1))=_
  rw [window_limb original bases scalar family window part 0 familyBound windowLower windowBound partBound (by decide),
    window_limb original bases scalar family window part 1 familyBound windowLower windowBound partBound (by decide)]
  rfl

theorem prefix_limb (original : Nat → F) (bases : Nat → curve.Point) (scalar family point limb : Nat)
    (familyBound : family<2) (pointBound : point<3) (limbBound : limb<2) :
    seed original bases scalar (column family 0 point limb)=coordinate (hintPoint (bases family) scalar point) limb := by
  obtain ⟨lower,upper,familyEqual,pointEqual,limbEqual⟩ := prefix_decode family point limb familyBound pointBound limbBound
  rw [seed,if_pos ⟨lower,upper⟩,familyEqual,pointEqual,limbEqual]

theorem prefix_point (original : Nat → F) (bases : Nat → curve.Point) (scalar family point : Nat)
    (familyBound : family<2) (pointBound : point<3) :
    VariableWindowColumns449.columnPoint (seed original bases scalar) (column family 0 point 0)=
      hintPoint (bases family) scalar point := by
  change Group.Point.mk (seed original bases scalar (column family 0 point 0))
    (seed original bases scalar (column family 0 point 1))=_
  rw [prefix_limb original bases scalar family point 0 familyBound pointBound (by decide),
    prefix_limb original bases scalar family point 1 familyBound pointBound (by decide)]
  rfl

theorem completed_hint (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (column : Nat)
    (lower : 2253≤column) (upper : column≤3764) :
    IvkInverseSeed426.assignment original c w authInitial initial senderInitial receiverInitial column=original column := by
  unfold IvkInverseSeed426.assignment
  rw [AuthorizationMultiplyFrame424.completed_hint _ c w authInitial initial senderInitial receiverInitial column
    (by constructor <;> omega)]
  exact IvkInverseSeed426.outside original w column (by omega)

theorem completed_point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (column : Nat)
    (lower : 2253≤column) (upper : column≤3763) :
    VariableWindowColumns449.columnPoint
      (IvkInverseSeed426.assignment original c w authInitial initial senderInitial receiverInitial) column=
      VariableWindowColumns449.columnPoint original column := by
  unfold VariableWindowColumns449.columnPoint
  rw [completed_hint original c w authInitial initial senderInitial receiverInitial column lower (by omega),
    completed_hint original c w authInitial initial senderInitial receiverInitial (column+1) (by omega) (by omega)]
end ShielddSecurity.AuthorizationTraceSeed451

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceSeed451.empty
#print axioms ShielddSecurity.AuthorizationTraceSeed451.empty

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceSeed451.trace
#print axioms ShielddSecurity.AuthorizationTraceSeed451.trace

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceSeed451.windowAt
#print axioms ShielddSecurity.AuthorizationTraceSeed451.windowAt

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceSeed451.component
#print axioms ShielddSecurity.AuthorizationTraceSeed451.component

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceSeed451.hintPoint
#print axioms ShielddSecurity.AuthorizationTraceSeed451.hintPoint

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceSeed451.coordinate
#print axioms ShielddSecurity.AuthorizationTraceSeed451.coordinate

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceSeed451.seed
#print axioms ShielddSecurity.AuthorizationTraceSeed451.seed

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceSeed451.outside
#print axioms ShielddSecurity.AuthorizationTraceSeed451.outside

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceSeed451.window_limb
#print axioms ShielddSecurity.AuthorizationTraceSeed451.window_limb

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceSeed451.window_point
#print axioms ShielddSecurity.AuthorizationTraceSeed451.window_point

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceSeed451.prefix_limb
#print axioms ShielddSecurity.AuthorizationTraceSeed451.prefix_limb

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceSeed451.prefix_point
#print axioms ShielddSecurity.AuthorizationTraceSeed451.prefix_point

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceSeed451.completed_hint
#print axioms ShielddSecurity.AuthorizationTraceSeed451.completed_hint

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceSeed451.completed_point
#print axioms ShielddSecurity.AuthorizationTraceSeed451.completed_point
