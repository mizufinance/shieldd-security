import ShielddSecurity.WordHints210
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedWordSlots211B015
open WordHints210 CompilerAssertionBlock51 CompilerArithmeticTransport41
namespace W60
def slot : Slot := ⟨21394,21199,128,4281⟩
def first : Nat := 21266
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^128) (meaning : base 4281=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 199348=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^128 ∧ (n : F)=rho 4281 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W60
namespace W61
def slot : Slot := ⟨21523,21327,128,4534⟩
def first : Nat := 21395
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^128) (meaning : base 4534=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 199477=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^128 ∧ (n : F)=rho 4534 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W61
namespace W62
def slot : Slot := ⟨21652,21455,128,4789⟩
def first : Nat := 21524
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^128) (meaning : base 4789=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 199606=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^128 ∧ (n : F)=rho 4789 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W62
namespace W63
def slot : Slot := ⟨21781,21583,128,6194⟩
def first : Nat := 21653
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^128) (meaning : base 6194=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 199735=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^128 ∧ (n : F)=rho 6194 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W63
end ShielddSecurity.CapturedWordSlots211B015

set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W60.slot
#print axioms ShielddSecurity.CapturedWordSlots211B015.W60.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W60.first
#print axioms ShielddSecurity.CapturedWordSlots211B015.W60.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W60.checked
#print axioms ShielddSecurity.CapturedWordSlots211B015.W60.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W60.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B015.W60.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W60.positions
#print axioms ShielddSecurity.CapturedWordSlots211B015.W60.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W60.originals
#print axioms ShielddSecurity.CapturedWordSlots211B015.W60.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W60.outside
#print axioms ShielddSecurity.CapturedWordSlots211B015.W60.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W60.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B015.W60.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W60.sound
#print axioms ShielddSecurity.CapturedWordSlots211B015.W60.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W61.slot
#print axioms ShielddSecurity.CapturedWordSlots211B015.W61.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W61.first
#print axioms ShielddSecurity.CapturedWordSlots211B015.W61.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W61.checked
#print axioms ShielddSecurity.CapturedWordSlots211B015.W61.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W61.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B015.W61.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W61.positions
#print axioms ShielddSecurity.CapturedWordSlots211B015.W61.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W61.originals
#print axioms ShielddSecurity.CapturedWordSlots211B015.W61.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W61.outside
#print axioms ShielddSecurity.CapturedWordSlots211B015.W61.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W61.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B015.W61.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W61.sound
#print axioms ShielddSecurity.CapturedWordSlots211B015.W61.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W62.slot
#print axioms ShielddSecurity.CapturedWordSlots211B015.W62.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W62.first
#print axioms ShielddSecurity.CapturedWordSlots211B015.W62.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W62.checked
#print axioms ShielddSecurity.CapturedWordSlots211B015.W62.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W62.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B015.W62.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W62.positions
#print axioms ShielddSecurity.CapturedWordSlots211B015.W62.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W62.originals
#print axioms ShielddSecurity.CapturedWordSlots211B015.W62.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W62.outside
#print axioms ShielddSecurity.CapturedWordSlots211B015.W62.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W62.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B015.W62.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W62.sound
#print axioms ShielddSecurity.CapturedWordSlots211B015.W62.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W63.slot
#print axioms ShielddSecurity.CapturedWordSlots211B015.W63.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W63.first
#print axioms ShielddSecurity.CapturedWordSlots211B015.W63.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W63.checked
#print axioms ShielddSecurity.CapturedWordSlots211B015.W63.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W63.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B015.W63.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W63.positions
#print axioms ShielddSecurity.CapturedWordSlots211B015.W63.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W63.originals
#print axioms ShielddSecurity.CapturedWordSlots211B015.W63.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W63.outside
#print axioms ShielddSecurity.CapturedWordSlots211B015.W63.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W63.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B015.W63.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B015.W63.sound
#print axioms ShielddSecurity.CapturedWordSlots211B015.W63.sound
