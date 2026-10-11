import ShielddSecurity.WordHints210
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedWordSlots211B002
open WordHints210 CompilerAssertionBlock51 CompilerArithmeticTransport41
namespace W08
def slot : Slot := ⟨1331,1244,127,1243⟩
def first : Nat := 1204
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^127) (meaning : base 1243=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 179285=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^127 ∧ (n : F)=rho 1243 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W08
namespace W09
def slot : Slot := ⟨1465,1375,128,1374⟩
def first : Nat := 1337
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^128) (meaning : base 1374=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 179419=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^128 ∧ (n : F)=rho 1374 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W09
namespace W10
def slot : Slot := ⟨1522,1579,32,1530⟩
def first : Nat := 1490
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^32) (meaning : base 1530=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 179476=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^32 ∧ (n : F)=rho 1530 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W10
namespace W11
def slot : Slot := ⟨1523,1579,32,1530⟩
def first : Nat := 1490
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^32) (meaning : base 1530=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 179477=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^32 ∧ (n : F)=rho 1530 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W11
end ShielddSecurity.CapturedWordSlots211B002

set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W08.slot
#print axioms ShielddSecurity.CapturedWordSlots211B002.W08.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W08.first
#print axioms ShielddSecurity.CapturedWordSlots211B002.W08.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W08.checked
#print axioms ShielddSecurity.CapturedWordSlots211B002.W08.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W08.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B002.W08.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W08.positions
#print axioms ShielddSecurity.CapturedWordSlots211B002.W08.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W08.originals
#print axioms ShielddSecurity.CapturedWordSlots211B002.W08.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W08.outside
#print axioms ShielddSecurity.CapturedWordSlots211B002.W08.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W08.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B002.W08.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W08.sound
#print axioms ShielddSecurity.CapturedWordSlots211B002.W08.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W09.slot
#print axioms ShielddSecurity.CapturedWordSlots211B002.W09.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W09.first
#print axioms ShielddSecurity.CapturedWordSlots211B002.W09.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W09.checked
#print axioms ShielddSecurity.CapturedWordSlots211B002.W09.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W09.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B002.W09.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W09.positions
#print axioms ShielddSecurity.CapturedWordSlots211B002.W09.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W09.originals
#print axioms ShielddSecurity.CapturedWordSlots211B002.W09.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W09.outside
#print axioms ShielddSecurity.CapturedWordSlots211B002.W09.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W09.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B002.W09.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W09.sound
#print axioms ShielddSecurity.CapturedWordSlots211B002.W09.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W10.slot
#print axioms ShielddSecurity.CapturedWordSlots211B002.W10.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W10.first
#print axioms ShielddSecurity.CapturedWordSlots211B002.W10.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W10.checked
#print axioms ShielddSecurity.CapturedWordSlots211B002.W10.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W10.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B002.W10.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W10.positions
#print axioms ShielddSecurity.CapturedWordSlots211B002.W10.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W10.originals
#print axioms ShielddSecurity.CapturedWordSlots211B002.W10.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W10.outside
#print axioms ShielddSecurity.CapturedWordSlots211B002.W10.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W10.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B002.W10.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W10.sound
#print axioms ShielddSecurity.CapturedWordSlots211B002.W10.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W11.slot
#print axioms ShielddSecurity.CapturedWordSlots211B002.W11.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W11.first
#print axioms ShielddSecurity.CapturedWordSlots211B002.W11.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W11.checked
#print axioms ShielddSecurity.CapturedWordSlots211B002.W11.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W11.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B002.W11.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W11.positions
#print axioms ShielddSecurity.CapturedWordSlots211B002.W11.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W11.originals
#print axioms ShielddSecurity.CapturedWordSlots211B002.W11.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W11.outside
#print axioms ShielddSecurity.CapturedWordSlots211B002.W11.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W11.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B002.W11.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B002.W11.sound
#print axioms ShielddSecurity.CapturedWordSlots211B002.W11.sound
