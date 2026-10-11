import ShielddSecurity.WordHints210
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedWordSlots211B003
open WordHints210 CompilerAssertionBlock51 CompilerArithmeticTransport41
namespace W12
def slot : Slot := ⟨1656,1611,131,1529⟩
def first : Nat := 1525
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^131) (meaning : base 1529=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 179610=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^131 ∧ (n : F)=rho 1529 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W12
namespace W13
def slot : Slot := ⟨1777,1817,32,1768⟩
def first : Nat := 1745
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^32) (meaning : base 1768=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 179731=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^32 ∧ (n : F)=rho 1768 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W13
namespace W14
def slot : Slot := ⟨1778,1817,32,1768⟩
def first : Nat := 1745
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^32) (meaning : base 1768=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 179732=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^32 ∧ (n : F)=rho 1768 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W14
namespace W15
def slot : Slot := ⟨1911,1849,131,1767⟩
def first : Nat := 1780
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^131) (meaning : base 1767=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 179865=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^131 ∧ (n : F)=rho 1767 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W15
end ShielddSecurity.CapturedWordSlots211B003

set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W12.slot
#print axioms ShielddSecurity.CapturedWordSlots211B003.W12.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W12.first
#print axioms ShielddSecurity.CapturedWordSlots211B003.W12.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W12.checked
#print axioms ShielddSecurity.CapturedWordSlots211B003.W12.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W12.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B003.W12.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W12.positions
#print axioms ShielddSecurity.CapturedWordSlots211B003.W12.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W12.originals
#print axioms ShielddSecurity.CapturedWordSlots211B003.W12.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W12.outside
#print axioms ShielddSecurity.CapturedWordSlots211B003.W12.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W12.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B003.W12.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W12.sound
#print axioms ShielddSecurity.CapturedWordSlots211B003.W12.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W13.slot
#print axioms ShielddSecurity.CapturedWordSlots211B003.W13.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W13.first
#print axioms ShielddSecurity.CapturedWordSlots211B003.W13.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W13.checked
#print axioms ShielddSecurity.CapturedWordSlots211B003.W13.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W13.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B003.W13.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W13.positions
#print axioms ShielddSecurity.CapturedWordSlots211B003.W13.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W13.originals
#print axioms ShielddSecurity.CapturedWordSlots211B003.W13.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W13.outside
#print axioms ShielddSecurity.CapturedWordSlots211B003.W13.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W13.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B003.W13.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W13.sound
#print axioms ShielddSecurity.CapturedWordSlots211B003.W13.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W14.slot
#print axioms ShielddSecurity.CapturedWordSlots211B003.W14.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W14.first
#print axioms ShielddSecurity.CapturedWordSlots211B003.W14.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W14.checked
#print axioms ShielddSecurity.CapturedWordSlots211B003.W14.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W14.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B003.W14.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W14.positions
#print axioms ShielddSecurity.CapturedWordSlots211B003.W14.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W14.originals
#print axioms ShielddSecurity.CapturedWordSlots211B003.W14.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W14.outside
#print axioms ShielddSecurity.CapturedWordSlots211B003.W14.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W14.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B003.W14.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W14.sound
#print axioms ShielddSecurity.CapturedWordSlots211B003.W14.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W15.slot
#print axioms ShielddSecurity.CapturedWordSlots211B003.W15.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W15.first
#print axioms ShielddSecurity.CapturedWordSlots211B003.W15.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W15.checked
#print axioms ShielddSecurity.CapturedWordSlots211B003.W15.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W15.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B003.W15.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W15.positions
#print axioms ShielddSecurity.CapturedWordSlots211B003.W15.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W15.originals
#print axioms ShielddSecurity.CapturedWordSlots211B003.W15.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W15.outside
#print axioms ShielddSecurity.CapturedWordSlots211B003.W15.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W15.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B003.W15.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B003.W15.sound
#print axioms ShielddSecurity.CapturedWordSlots211B003.W15.sound
