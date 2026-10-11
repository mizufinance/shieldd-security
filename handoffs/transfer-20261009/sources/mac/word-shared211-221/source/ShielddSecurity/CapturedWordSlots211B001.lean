import ShielddSecurity.WordHints210
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedWordSlots211B001
open WordHints210 CompilerAssertionBlock51 CompilerArithmeticTransport41
namespace W04
def slot : Slot := ⟨678,471,255,6⟩
def first : Nat := 423
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^255) (meaning : base 6=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 178632=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^255 ∧ (n : F)=rho 6 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W04
namespace W05
def slot : Slot := ⟨936,726,255,13⟩
def first : Nat := 681
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^255) (meaning : base 13=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 178890=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^255 ∧ (n : F)=rho 13 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W05
namespace W06
def slot : Slot := ⟨1067,983,127,982⟩
def first : Nat := 940
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^127) (meaning : base 982=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 179021=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^127 ∧ (n : F)=rho 982 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W06
namespace W07
def slot : Slot := ⟨1201,1114,128,1113⟩
def first : Nat := 1073
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^128) (meaning : base 1113=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 179155=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^128 ∧ (n : F)=rho 1113 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W07
end ShielddSecurity.CapturedWordSlots211B001

set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W04.slot
#print axioms ShielddSecurity.CapturedWordSlots211B001.W04.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W04.first
#print axioms ShielddSecurity.CapturedWordSlots211B001.W04.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W04.checked
#print axioms ShielddSecurity.CapturedWordSlots211B001.W04.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W04.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B001.W04.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W04.positions
#print axioms ShielddSecurity.CapturedWordSlots211B001.W04.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W04.originals
#print axioms ShielddSecurity.CapturedWordSlots211B001.W04.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W04.outside
#print axioms ShielddSecurity.CapturedWordSlots211B001.W04.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W04.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B001.W04.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W04.sound
#print axioms ShielddSecurity.CapturedWordSlots211B001.W04.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W05.slot
#print axioms ShielddSecurity.CapturedWordSlots211B001.W05.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W05.first
#print axioms ShielddSecurity.CapturedWordSlots211B001.W05.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W05.checked
#print axioms ShielddSecurity.CapturedWordSlots211B001.W05.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W05.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B001.W05.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W05.positions
#print axioms ShielddSecurity.CapturedWordSlots211B001.W05.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W05.originals
#print axioms ShielddSecurity.CapturedWordSlots211B001.W05.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W05.outside
#print axioms ShielddSecurity.CapturedWordSlots211B001.W05.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W05.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B001.W05.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W05.sound
#print axioms ShielddSecurity.CapturedWordSlots211B001.W05.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W06.slot
#print axioms ShielddSecurity.CapturedWordSlots211B001.W06.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W06.first
#print axioms ShielddSecurity.CapturedWordSlots211B001.W06.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W06.checked
#print axioms ShielddSecurity.CapturedWordSlots211B001.W06.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W06.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B001.W06.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W06.positions
#print axioms ShielddSecurity.CapturedWordSlots211B001.W06.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W06.originals
#print axioms ShielddSecurity.CapturedWordSlots211B001.W06.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W06.outside
#print axioms ShielddSecurity.CapturedWordSlots211B001.W06.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W06.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B001.W06.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W06.sound
#print axioms ShielddSecurity.CapturedWordSlots211B001.W06.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W07.slot
#print axioms ShielddSecurity.CapturedWordSlots211B001.W07.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W07.first
#print axioms ShielddSecurity.CapturedWordSlots211B001.W07.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W07.checked
#print axioms ShielddSecurity.CapturedWordSlots211B001.W07.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W07.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B001.W07.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W07.positions
#print axioms ShielddSecurity.CapturedWordSlots211B001.W07.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W07.originals
#print axioms ShielddSecurity.CapturedWordSlots211B001.W07.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W07.outside
#print axioms ShielddSecurity.CapturedWordSlots211B001.W07.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W07.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B001.W07.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B001.W07.sound
#print axioms ShielddSecurity.CapturedWordSlots211B001.W07.sound
