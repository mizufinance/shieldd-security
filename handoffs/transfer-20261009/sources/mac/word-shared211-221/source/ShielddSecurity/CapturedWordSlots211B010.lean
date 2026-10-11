import ShielddSecurity.WordHints210
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedWordSlots211B010
open WordHints210 CompilerAssertionBlock51 CompilerArithmeticTransport41
namespace W40
def slot : Slot := ⟨9092,9062,1,9059⟩
def first : Nat := 8834
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^1) (meaning : base 9059=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 187046=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^1 ∧ (n : F)=rho 9059 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W40
namespace W41
def slot : Slot := ⟨10111,10084,252,10083⟩
def first : Nat := 9859
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^252) (meaning : base 10083=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 188065=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^252 ∧ (n : F)=rho 10083 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W41
namespace W42
def slot : Slot := ⟨10629,10594,255,10593⟩
def first : Nat := 10374
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^255) (meaning : base 10593=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 188583=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^255 ∧ (n : F)=rho 10593 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W42
namespace W43
def slot : Slot := ⟨10632,10594,1,10591⟩
def first : Nat := 10374
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^1) (meaning : base 10591=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 188586=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^1 ∧ (n : F)=rho 10591 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W43
end ShielddSecurity.CapturedWordSlots211B010

set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W40.slot
#print axioms ShielddSecurity.CapturedWordSlots211B010.W40.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W40.first
#print axioms ShielddSecurity.CapturedWordSlots211B010.W40.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W40.checked
#print axioms ShielddSecurity.CapturedWordSlots211B010.W40.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W40.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B010.W40.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W40.positions
#print axioms ShielddSecurity.CapturedWordSlots211B010.W40.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W40.originals
#print axioms ShielddSecurity.CapturedWordSlots211B010.W40.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W40.outside
#print axioms ShielddSecurity.CapturedWordSlots211B010.W40.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W40.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B010.W40.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W40.sound
#print axioms ShielddSecurity.CapturedWordSlots211B010.W40.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W41.slot
#print axioms ShielddSecurity.CapturedWordSlots211B010.W41.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W41.first
#print axioms ShielddSecurity.CapturedWordSlots211B010.W41.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W41.checked
#print axioms ShielddSecurity.CapturedWordSlots211B010.W41.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W41.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B010.W41.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W41.positions
#print axioms ShielddSecurity.CapturedWordSlots211B010.W41.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W41.originals
#print axioms ShielddSecurity.CapturedWordSlots211B010.W41.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W41.outside
#print axioms ShielddSecurity.CapturedWordSlots211B010.W41.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W41.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B010.W41.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W41.sound
#print axioms ShielddSecurity.CapturedWordSlots211B010.W41.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W42.slot
#print axioms ShielddSecurity.CapturedWordSlots211B010.W42.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W42.first
#print axioms ShielddSecurity.CapturedWordSlots211B010.W42.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W42.checked
#print axioms ShielddSecurity.CapturedWordSlots211B010.W42.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W42.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B010.W42.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W42.positions
#print axioms ShielddSecurity.CapturedWordSlots211B010.W42.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W42.originals
#print axioms ShielddSecurity.CapturedWordSlots211B010.W42.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W42.outside
#print axioms ShielddSecurity.CapturedWordSlots211B010.W42.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W42.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B010.W42.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W42.sound
#print axioms ShielddSecurity.CapturedWordSlots211B010.W42.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W43.slot
#print axioms ShielddSecurity.CapturedWordSlots211B010.W43.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W43.first
#print axioms ShielddSecurity.CapturedWordSlots211B010.W43.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W43.checked
#print axioms ShielddSecurity.CapturedWordSlots211B010.W43.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W43.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B010.W43.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W43.positions
#print axioms ShielddSecurity.CapturedWordSlots211B010.W43.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W43.originals
#print axioms ShielddSecurity.CapturedWordSlots211B010.W43.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W43.outside
#print axioms ShielddSecurity.CapturedWordSlots211B010.W43.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W43.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B010.W43.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B010.W43.sound
#print axioms ShielddSecurity.CapturedWordSlots211B010.W43.sound
