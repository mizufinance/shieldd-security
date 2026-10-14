-- GENERATED from maintained exact capture; do not edit.
import ShielddSecurity.VolumeControlCapture804F0
import ShielddSecurity.VolumeControlCapture804F1
import ShielddSecurity.VolumeControlCapture804F2
import ShielddSecurity.VolumeControlCapture804F3
import ShielddSecurity.VolumeControlCapture804Context
import ShielddSecurity.VolumeControlBindings803
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeControlCapture804
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 MapArithmeticAdapter704
def firstPosition (slot : Fin 4) : Nat := 7462+3*slot.val
def inverseOutput (slot : Fin 4) : Nat := if slot.val=0 then 108438 else if slot.val=1 then 108442 else if slot.val=2 then 108448 else 108454
def zeroOutput (slot : Fin 4) : Nat := if slot.val=0 then 108440 else if slot.val=1 then 108444 else if slot.val=2 then 108450 else 108456

def FamilyRows (rho : Nat → F) (slot : Fin 4) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+firstPosition slot+i)) 1 ∧
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+firstPosition slot+1+i)) 1

def Rows (rho : Nat → F) : Prop :=
  (∀ slot : Fin 4,FamilyRows rho slot) ∧ SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+7475+i)) 1

theorem equations (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (slot : Fin 4) :
    rho (inverseOutput slot)=(rho (VolumeControlBindings803.leftColumn slot)-rho (VolumeControlBindings803.rightColumn slot))*rho (7598+2*slot.val) ∧
    rho (zeroOutput slot)=(rho (VolumeControlBindings803.leftColumn slot)-rho (VolumeControlBindings803.rightColumn slot))*rho (7597+2*slot.val) := by
  rcases slot with ⟨slot,bound⟩
  have cases : slot=0 ∨ slot=1 ∨ slot=2 ∨ slot=3 := by omega
  rcases cases with rfl|rfl|rfl|rfl
  · exact ⟨VolumeControlCapture804F0.inverse_equation rho arithmetic,VolumeControlCapture804F0.zero_equation rho arithmetic⟩
  · exact ⟨VolumeControlCapture804F1.inverse_equation rho arithmetic,VolumeControlCapture804F1.zero_equation rho arithmetic⟩
  · exact ⟨VolumeControlCapture804F2.inverse_equation rho arithmetic,VolumeControlCapture804F2.zero_equation rho arithmetic⟩
  · exact ⟨VolumeControlCapture804F3.inverse_equation rho arithmetic,VolumeControlCapture804F3.zero_equation rho arithmetic⟩

theorem family_rows (rho : Nat → F) (one : rho copy=1) (slot : Fin 4)
    (inverse : rho (inverseOutput slot)=1-rho (7597+2*slot.val)) (zero : rho (zeroOutput slot)=0) : FamilyRows rho slot := by
  rcases slot with ⟨slot,bound⟩
  have cases : slot=0 ∨ slot=1 ∨ slot=2 ∨ slot=3 := by omega
  rcases cases with rfl|rfl|rfl|rfl
  · exact VolumeControlCapture804F0.rows rho one inverse zero
  · exact VolumeControlCapture804F1.rows rho one inverse zero
  · exact VolumeControlCapture804F2.rows rho one inverse zero
  · exact VolumeControlCapture804F3.rows rho one inverse zero

theorem rows (rho : Nat → F) (one : rho copy=1)
    (families : ∀ slot : Fin 4,FamilyRows rho slot)
    (boolean : (rho 7607-1)*(rho 7607-1)=rho 7607-1) : Rows rho :=
  ⟨families,VolumeControlCapture804Context.satisfies rho one boolean⟩
end ShielddSecurity.VolumeControlCapture804

set_option pp.all true in
#check @ShielddSecurity.VolumeControlCapture804.FamilyRows
#print axioms ShielddSecurity.VolumeControlCapture804.FamilyRows

set_option pp.all true in
#check @ShielddSecurity.VolumeControlCapture804.Rows
#print axioms ShielddSecurity.VolumeControlCapture804.Rows

set_option pp.all true in
#check @ShielddSecurity.VolumeControlCapture804.equations
#print axioms ShielddSecurity.VolumeControlCapture804.equations

set_option pp.all true in
#check @ShielddSecurity.VolumeControlCapture804.family_rows
#print axioms ShielddSecurity.VolumeControlCapture804.family_rows

set_option pp.all true in
#check @ShielddSecurity.VolumeControlCapture804.rows
#print axioms ShielddSecurity.VolumeControlCapture804.rows
