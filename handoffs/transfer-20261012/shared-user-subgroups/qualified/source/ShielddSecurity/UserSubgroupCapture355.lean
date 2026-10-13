import ShielddSecurity.UserSubgroupCapture355B00
import ShielddSecurity.UserSubgroupCapture355B01
import ShielddSecurity.UserSubgroupCapture355B02
import ShielddSecurity.UserSubgroupCapture355B03
import ShielddSecurity.UserSubgroupCapture355B04
import ShielddSecurity.UserSubgroupCapture355B05
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserSubgroupCapture355
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
def rename (group : Fin 6) : Nat → Nat :=
  if group.val=0 then UserSubgroupCapture355B00.rename
  else if group.val=1 then UserSubgroupCapture355B01.rename
  else if group.val=2 then UserSubgroupCapture355B02.rename
  else if group.val=3 then UserSubgroupCapture355B03.rename
  else if group.val=4 then UserSubgroupCapture355B04.rename
  else UserSubgroupCapture355B05.rename
def assertionStart (group : Fin 6) : Nat :=
  if group.val=0 then 1469
  else if group.val=1 then 1476
  else if group.val=2 then 1483
  else if group.val=3 then 1724
  else if group.val=4 then 1731
  else 1738
variable {F : Type} [Field F] [CharP F p]
def Rows (rho : Nat → F) : Prop := ∀ group : Fin 6,
  SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (177954+assertionStart group+index)) 6

theorem complete (rho : Nat → F) (initial : Fin 6 → Group.Point F) (imaginary : F)
    (zero : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (roles : ∀ group,CapturedFourSubgroupConstructor88.InputRoles (fun column => rho (rename group column)) (initial group))
    (valid : ∀ group,Group.OnCurve (CapturedFirstSubgroup81.d:F) (initial group))
    (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F)) (imaginarySquare : imaginary*imaginary=-1) : Rows rho := by
  intro group
  rcases group with ⟨group,bound⟩
  have cases : group=0 ∨ group=1 ∨ group=2 ∨ group=3 ∨ group=4 ∨ group=5 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · exact UserSubgroupCapture355B00.complete rho (initial ⟨0,by decide⟩) imaginary zero linked arithmetic (roles ⟨0,by decide⟩) (valid ⟨0,by decide⟩) nonSquare imaginarySquare
  · exact UserSubgroupCapture355B01.complete rho (initial ⟨1,by decide⟩) imaginary zero linked arithmetic (roles ⟨1,by decide⟩) (valid ⟨1,by decide⟩) nonSquare imaginarySquare
  · exact UserSubgroupCapture355B02.complete rho (initial ⟨2,by decide⟩) imaginary zero linked arithmetic (roles ⟨2,by decide⟩) (valid ⟨2,by decide⟩) nonSquare imaginarySquare
  · exact UserSubgroupCapture355B03.complete rho (initial ⟨3,by decide⟩) imaginary zero linked arithmetic (roles ⟨3,by decide⟩) (valid ⟨3,by decide⟩) nonSquare imaginarySquare
  · exact UserSubgroupCapture355B04.complete rho (initial ⟨4,by decide⟩) imaginary zero linked arithmetic (roles ⟨4,by decide⟩) (valid ⟨4,by decide⟩) nonSquare imaginarySquare
  · exact UserSubgroupCapture355B05.complete rho (initial ⟨5,by decide⟩) imaginary zero linked arithmetic (roles ⟨5,by decide⟩) (valid ⟨5,by decide⟩) nonSquare imaginarySquare
end ShielddSecurity.UserSubgroupCapture355

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupCapture355.rename
#print axioms ShielddSecurity.UserSubgroupCapture355.rename

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupCapture355.assertionStart
#print axioms ShielddSecurity.UserSubgroupCapture355.assertionStart

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupCapture355.Rows
#print axioms ShielddSecurity.UserSubgroupCapture355.Rows

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupCapture355.complete
#print axioms ShielddSecurity.UserSubgroupCapture355.complete
