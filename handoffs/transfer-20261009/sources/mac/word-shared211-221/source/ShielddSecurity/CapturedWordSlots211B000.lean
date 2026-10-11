import ShielddSecurity.WordHints210
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedWordSlots211B000
open WordHints210 CompilerAssertionBlock51 CompilerArithmeticTransport41
namespace W00
def slot : Slot := ⟨89,49,64,34⟩
def first : Nat := 25
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^64) (meaning : base 34=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 178043=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^64 ∧ (n : F)=rho 34 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W00
namespace W01
def slot : Slot := ⟨161,184,32,135⟩
def first : Nat := 129
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^32) (meaning : base 135=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 178115=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^32 ∧ (n : F)=rho 135 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W01
namespace W02
def slot : Slot := ⟨162,184,32,135⟩
def first : Nat := 129
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^32) (meaning : base 135=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 178116=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^32 ∧ (n : F)=rho 135 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W02
namespace W03
def slot : Slot := ⟨420,216,255,11⟩
def first : Nat := 165
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^255) (meaning : base 11=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 178374=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^255 ∧ (n : F)=rho 11 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W03
end ShielddSecurity.CapturedWordSlots211B000

set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W00.slot
#print axioms ShielddSecurity.CapturedWordSlots211B000.W00.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W00.first
#print axioms ShielddSecurity.CapturedWordSlots211B000.W00.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W00.checked
#print axioms ShielddSecurity.CapturedWordSlots211B000.W00.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W00.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B000.W00.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W00.positions
#print axioms ShielddSecurity.CapturedWordSlots211B000.W00.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W00.originals
#print axioms ShielddSecurity.CapturedWordSlots211B000.W00.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W00.outside
#print axioms ShielddSecurity.CapturedWordSlots211B000.W00.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W00.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B000.W00.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W00.sound
#print axioms ShielddSecurity.CapturedWordSlots211B000.W00.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W01.slot
#print axioms ShielddSecurity.CapturedWordSlots211B000.W01.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W01.first
#print axioms ShielddSecurity.CapturedWordSlots211B000.W01.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W01.checked
#print axioms ShielddSecurity.CapturedWordSlots211B000.W01.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W01.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B000.W01.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W01.positions
#print axioms ShielddSecurity.CapturedWordSlots211B000.W01.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W01.originals
#print axioms ShielddSecurity.CapturedWordSlots211B000.W01.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W01.outside
#print axioms ShielddSecurity.CapturedWordSlots211B000.W01.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W01.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B000.W01.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W01.sound
#print axioms ShielddSecurity.CapturedWordSlots211B000.W01.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W02.slot
#print axioms ShielddSecurity.CapturedWordSlots211B000.W02.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W02.first
#print axioms ShielddSecurity.CapturedWordSlots211B000.W02.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W02.checked
#print axioms ShielddSecurity.CapturedWordSlots211B000.W02.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W02.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B000.W02.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W02.positions
#print axioms ShielddSecurity.CapturedWordSlots211B000.W02.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W02.originals
#print axioms ShielddSecurity.CapturedWordSlots211B000.W02.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W02.outside
#print axioms ShielddSecurity.CapturedWordSlots211B000.W02.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W02.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B000.W02.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W02.sound
#print axioms ShielddSecurity.CapturedWordSlots211B000.W02.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W03.slot
#print axioms ShielddSecurity.CapturedWordSlots211B000.W03.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W03.first
#print axioms ShielddSecurity.CapturedWordSlots211B000.W03.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W03.checked
#print axioms ShielddSecurity.CapturedWordSlots211B000.W03.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W03.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B000.W03.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W03.positions
#print axioms ShielddSecurity.CapturedWordSlots211B000.W03.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W03.originals
#print axioms ShielddSecurity.CapturedWordSlots211B000.W03.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W03.outside
#print axioms ShielddSecurity.CapturedWordSlots211B000.W03.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W03.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B000.W03.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B000.W03.sound
#print axioms ShielddSecurity.CapturedWordSlots211B000.W03.sound
