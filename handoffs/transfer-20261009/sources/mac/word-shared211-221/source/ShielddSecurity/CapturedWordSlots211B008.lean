import ShielddSecurity.WordHints210
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedWordSlots211B008
open WordHints210 CompilerAssertionBlock51 CompilerArithmeticTransport41
namespace W32
def slot : Slot := ⟨7742,7743,128,7741⟩
def first : Nat := 7614
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^128) (meaning : base 7741=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 185696=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^128 ∧ (n : F)=rho 7741 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W32
namespace W33
def slot : Slot := ⟨7871,7871,128,7742⟩
def first : Nat := 7743
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^128) (meaning : base 7742=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 185825=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^128 ∧ (n : F)=rho 7742 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W33
namespace W34
def slot : Slot := ⟨8000,7999,128,21⟩
def first : Nat := 7872
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^128) (meaning : base 21=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 185954=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^128 ∧ (n : F)=rho 21 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W34
namespace W35
def slot : Slot := ⟨8260,8257,128,8256⟩
def first : Nat := 8132
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^128) (meaning : base 8256=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 186214=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^128 ∧ (n : F)=rho 8256 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W35
end ShielddSecurity.CapturedWordSlots211B008

set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W32.slot
#print axioms ShielddSecurity.CapturedWordSlots211B008.W32.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W32.first
#print axioms ShielddSecurity.CapturedWordSlots211B008.W32.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W32.checked
#print axioms ShielddSecurity.CapturedWordSlots211B008.W32.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W32.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B008.W32.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W32.positions
#print axioms ShielddSecurity.CapturedWordSlots211B008.W32.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W32.originals
#print axioms ShielddSecurity.CapturedWordSlots211B008.W32.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W32.outside
#print axioms ShielddSecurity.CapturedWordSlots211B008.W32.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W32.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B008.W32.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W32.sound
#print axioms ShielddSecurity.CapturedWordSlots211B008.W32.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W33.slot
#print axioms ShielddSecurity.CapturedWordSlots211B008.W33.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W33.first
#print axioms ShielddSecurity.CapturedWordSlots211B008.W33.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W33.checked
#print axioms ShielddSecurity.CapturedWordSlots211B008.W33.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W33.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B008.W33.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W33.positions
#print axioms ShielddSecurity.CapturedWordSlots211B008.W33.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W33.originals
#print axioms ShielddSecurity.CapturedWordSlots211B008.W33.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W33.outside
#print axioms ShielddSecurity.CapturedWordSlots211B008.W33.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W33.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B008.W33.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W33.sound
#print axioms ShielddSecurity.CapturedWordSlots211B008.W33.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W34.slot
#print axioms ShielddSecurity.CapturedWordSlots211B008.W34.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W34.first
#print axioms ShielddSecurity.CapturedWordSlots211B008.W34.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W34.checked
#print axioms ShielddSecurity.CapturedWordSlots211B008.W34.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W34.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B008.W34.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W34.positions
#print axioms ShielddSecurity.CapturedWordSlots211B008.W34.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W34.originals
#print axioms ShielddSecurity.CapturedWordSlots211B008.W34.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W34.outside
#print axioms ShielddSecurity.CapturedWordSlots211B008.W34.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W34.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B008.W34.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W34.sound
#print axioms ShielddSecurity.CapturedWordSlots211B008.W34.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W35.slot
#print axioms ShielddSecurity.CapturedWordSlots211B008.W35.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W35.first
#print axioms ShielddSecurity.CapturedWordSlots211B008.W35.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W35.checked
#print axioms ShielddSecurity.CapturedWordSlots211B008.W35.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W35.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B008.W35.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W35.positions
#print axioms ShielddSecurity.CapturedWordSlots211B008.W35.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W35.originals
#print axioms ShielddSecurity.CapturedWordSlots211B008.W35.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W35.outside
#print axioms ShielddSecurity.CapturedWordSlots211B008.W35.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W35.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B008.W35.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B008.W35.sound
#print axioms ShielddSecurity.CapturedWordSlots211B008.W35.sound
