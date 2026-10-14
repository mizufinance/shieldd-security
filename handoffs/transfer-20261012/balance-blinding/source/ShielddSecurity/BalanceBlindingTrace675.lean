import ShielddSecurity.BalanceBlindingDomain670
import ShielddSecurity.FixedTraceAccess486
import ShielddSecurity.VariableWindowColumns449
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingTrace675
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

noncomputable def empty : GroupFixedWindows.FixedWindowWitness F :=
  ⟨false,false,Group.identityPoint,Group.identityPoint,Group.identityPoint,Group.identityPoint⟩
noncomputable def trace (scalar : Nat) : List (GroupFixedWindows.FixedWindowWitness F) :=
  FixedTraceConstruction478.windows model BalanceBlindingDomain670.represented (encodeBits 252 scalar)
noncomputable def window (scalar index : Nat) : GroupFixedWindows.FixedWindowWitness F := (trace scalar)[index]?.getD empty

noncomputable def seed (original : Nat → F) (scalar column : Nat) : F :=
  if 22484≤column ∧ column≤22735 then
    let output := (window scalar ((column-22484)/2)).output
    if (column-22484)%2=0 then output.x else output.y
  else original column

theorem outside (original : Nat → F) (scalar column : Nat) (out : column<22484 ∨ 22735<column) :
    seed original scalar column=original column := by
  simp only [seed,if_neg (show ¬(22484≤column ∧ column≤22735) by omega)]

theorem limb (original : Nat → F) (scalar index limb : Nat) (before : index<126) (small : limb<2) :
    seed original scalar (22484+2*index+limb)=
      if limb=0 then (window scalar index).output.x else (window scalar index).output.y := by
  have bounds : 22484≤22484+2*index+limb ∧ 22484+2*index+limb≤22735 := by omega
  have quotient : (22484+2*index+limb-22484)/2=index := by omega
  have remainder : (22484+2*index+limb-22484)%2=limb := by omega
  simp only [seed,if_pos bounds,quotient,remainder]

theorem point (original : Nat → F) (scalar index : Nat) (before : index<126) :
    VariableWindowColumns449.columnPoint (seed original scalar) (22484+2*index)=(window scalar index).output := by
  have x := limb original scalar index 0 before (by decide)
  have y := limb original scalar index 1 before (by decide)
  change seed original scalar (22484+2*index)=(window scalar index).output.x at x
  change seed original scalar (22484+2*index+1)=(window scalar index).output.y at y
  cases output : (window scalar index).output with
  | mk px py =>
    simp only [output] at x y
    exact congrArg₂ Group.Point.mk x y

end ShielddSecurity.BalanceBlindingTrace675

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingTrace675.empty
#print axioms ShielddSecurity.BalanceBlindingTrace675.empty

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingTrace675.trace
#print axioms ShielddSecurity.BalanceBlindingTrace675.trace

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingTrace675.window
#print axioms ShielddSecurity.BalanceBlindingTrace675.window

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingTrace675.seed
#print axioms ShielddSecurity.BalanceBlindingTrace675.seed

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingTrace675.outside
#print axioms ShielddSecurity.BalanceBlindingTrace675.outside

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingTrace675.limb
#print axioms ShielddSecurity.BalanceBlindingTrace675.limb

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingTrace675.point
#print axioms ShielddSecurity.BalanceBlindingTrace675.point
