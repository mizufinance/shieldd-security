import ShielddSecurity.AuthorizationPointDomain404
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationPointSeed405
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def value (w : TransferSem.Witness) (initial : Group.Point F) (offset : Nat) : F :=
  if offset=0 then (w.auth.ak.x:F)
  else if offset=1 then (w.auth.ak.y:F)
  else if offset=2 then initial.x
  else if offset=3 then initial.y
  else if offset<7 then CompilerSubgroupArithmetic79.hints (CapturedFirstSubgroup81.d:F) initial (offset-4)
  else (w.auth.ak.x:F)⁻¹

def seed (original : Nat → F) (w : TransferSem.Witness) (initial : Group.Point F) (column : Nat) : F :=
  if 1980≤column ∧ column<1988 then value w initial (column-1980)
  else if column=1993 then (w.auth.nk:F)
  else original column

theorem outside (original : Nat → F) (w : TransferSem.Witness) (initial : Group.Point F) (column : Nat)
    (point : ¬(1980≤column ∧ column<1988)) (key : column≠1993) :
    seed original w initial column=original column := by
  simp only [seed,if_neg point,if_neg key]

theorem point_value (original : Nat → F) (w : TransferSem.Witness) (initial : Group.Point F) (offset : Fin 8) :
    seed original w initial (1980+offset.val)=value w initial offset.val := by
  have inside : 1980≤1980+offset.val ∧1980+offset.val<1988 := by have := offset.isLt; omega
  rw [seed,if_pos inside,Nat.add_sub_cancel_left]

theorem key_value (original : Nat → F) (w : TransferSem.Witness) (initial : Group.Point F) :
    seed original w initial 1993=(w.auth.nk:F) := by rfl

theorem inverse_equation (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) (initial : Group.Point F) :
    seed original w initial 1980*seed original w initial 1987=1 := by
  have first := point_value original w initial ⟨0,by decide⟩
  have inverse := point_value original w initial ⟨7,by decide⟩
  change seed original w initial 1980=(w.auth.ak.x:F) at first
  change seed original w initial 1987=(w.auth.ak.x:F)⁻¹ at inverse
  rw [first,inverse]
  exact AuthorizationPointDomain404.inverse_equation c w legal

end ShielddSecurity.AuthorizationPointSeed405

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointSeed405.value
#print axioms ShielddSecurity.AuthorizationPointSeed405.value

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointSeed405.seed
#print axioms ShielddSecurity.AuthorizationPointSeed405.seed

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointSeed405.outside
#print axioms ShielddSecurity.AuthorizationPointSeed405.outside

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointSeed405.point_value
#print axioms ShielddSecurity.AuthorizationPointSeed405.point_value

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointSeed405.key_value
#print axioms ShielddSecurity.AuthorizationPointSeed405.key_value

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointSeed405.inverse_equation
#print axioms ShielddSecurity.AuthorizationPointSeed405.inverse_equation
