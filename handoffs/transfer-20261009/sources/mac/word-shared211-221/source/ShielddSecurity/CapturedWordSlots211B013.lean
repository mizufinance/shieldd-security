import ShielddSecurity.WordHints210
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedWordSlots211B013
open WordHints210 CompilerAssertionBlock51 CompilerArithmeticTransport41
namespace W52
def slot : Slot := ⟨18517,18435,255,1505⟩
def first : Nat := 18262
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^255) (meaning : base 1505=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 196471=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^255 ∧ (n : F)=rho 1505 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W52
namespace W53
def slot : Slot := ⟨18775,18690,255,1504⟩
def first : Nat := 18520
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^255) (meaning : base 1504=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 196729=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^255 ∧ (n : F)=rho 1504 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W53
namespace W54
def slot : Slot := ⟨19033,18945,255,1513⟩
def first : Nat := 18778
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^255) (meaning : base 1513=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 196987=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^255 ∧ (n : F)=rho 1513 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W54
namespace W55
def slot : Slot := ⟨19291,19200,255,1512⟩
def first : Nat := 19036
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^255) (meaning : base 1512=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 197245=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^255 ∧ (n : F)=rho 1512 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W55
end ShielddSecurity.CapturedWordSlots211B013

set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W52.slot
#print axioms ShielddSecurity.CapturedWordSlots211B013.W52.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W52.first
#print axioms ShielddSecurity.CapturedWordSlots211B013.W52.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W52.checked
#print axioms ShielddSecurity.CapturedWordSlots211B013.W52.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W52.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B013.W52.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W52.positions
#print axioms ShielddSecurity.CapturedWordSlots211B013.W52.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W52.originals
#print axioms ShielddSecurity.CapturedWordSlots211B013.W52.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W52.outside
#print axioms ShielddSecurity.CapturedWordSlots211B013.W52.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W52.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B013.W52.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W52.sound
#print axioms ShielddSecurity.CapturedWordSlots211B013.W52.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W53.slot
#print axioms ShielddSecurity.CapturedWordSlots211B013.W53.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W53.first
#print axioms ShielddSecurity.CapturedWordSlots211B013.W53.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W53.checked
#print axioms ShielddSecurity.CapturedWordSlots211B013.W53.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W53.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B013.W53.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W53.positions
#print axioms ShielddSecurity.CapturedWordSlots211B013.W53.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W53.originals
#print axioms ShielddSecurity.CapturedWordSlots211B013.W53.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W53.outside
#print axioms ShielddSecurity.CapturedWordSlots211B013.W53.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W53.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B013.W53.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W53.sound
#print axioms ShielddSecurity.CapturedWordSlots211B013.W53.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W54.slot
#print axioms ShielddSecurity.CapturedWordSlots211B013.W54.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W54.first
#print axioms ShielddSecurity.CapturedWordSlots211B013.W54.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W54.checked
#print axioms ShielddSecurity.CapturedWordSlots211B013.W54.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W54.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B013.W54.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W54.positions
#print axioms ShielddSecurity.CapturedWordSlots211B013.W54.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W54.originals
#print axioms ShielddSecurity.CapturedWordSlots211B013.W54.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W54.outside
#print axioms ShielddSecurity.CapturedWordSlots211B013.W54.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W54.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B013.W54.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W54.sound
#print axioms ShielddSecurity.CapturedWordSlots211B013.W54.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W55.slot
#print axioms ShielddSecurity.CapturedWordSlots211B013.W55.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W55.first
#print axioms ShielddSecurity.CapturedWordSlots211B013.W55.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W55.checked
#print axioms ShielddSecurity.CapturedWordSlots211B013.W55.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W55.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B013.W55.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W55.positions
#print axioms ShielddSecurity.CapturedWordSlots211B013.W55.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W55.originals
#print axioms ShielddSecurity.CapturedWordSlots211B013.W55.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W55.outside
#print axioms ShielddSecurity.CapturedWordSlots211B013.W55.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W55.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B013.W55.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B013.W55.sound
#print axioms ShielddSecurity.CapturedWordSlots211B013.W55.sound
