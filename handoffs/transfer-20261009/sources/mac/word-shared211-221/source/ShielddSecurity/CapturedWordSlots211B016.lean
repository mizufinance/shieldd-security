import ShielddSecurity.WordHints210
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedWordSlots211B016
open WordHints210 CompilerAssertionBlock51 CompilerArithmeticTransport41
namespace W64
def slot : Slot := ⟨21912,21713,129,21712⟩
def first : Nat := 21783
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^129) (meaning : base 21712=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 199866=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^129 ∧ (n : F)=rho 21712 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W64
namespace W65
def slot : Slot := ⟨22556,22232,252,9⟩
def first : Nat := 22304
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^252) (meaning : base 9=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 200510=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^252 ∧ (n : F)=rho 9 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W65
end ShielddSecurity.CapturedWordSlots211B016

set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B016.W64.slot
#print axioms ShielddSecurity.CapturedWordSlots211B016.W64.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B016.W64.first
#print axioms ShielddSecurity.CapturedWordSlots211B016.W64.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B016.W64.checked
#print axioms ShielddSecurity.CapturedWordSlots211B016.W64.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B016.W64.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B016.W64.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B016.W64.positions
#print axioms ShielddSecurity.CapturedWordSlots211B016.W64.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B016.W64.originals
#print axioms ShielddSecurity.CapturedWordSlots211B016.W64.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B016.W64.outside
#print axioms ShielddSecurity.CapturedWordSlots211B016.W64.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B016.W64.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B016.W64.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B016.W64.sound
#print axioms ShielddSecurity.CapturedWordSlots211B016.W64.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B016.W65.slot
#print axioms ShielddSecurity.CapturedWordSlots211B016.W65.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B016.W65.first
#print axioms ShielddSecurity.CapturedWordSlots211B016.W65.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B016.W65.checked
#print axioms ShielddSecurity.CapturedWordSlots211B016.W65.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B016.W65.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B016.W65.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B016.W65.positions
#print axioms ShielddSecurity.CapturedWordSlots211B016.W65.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B016.W65.originals
#print axioms ShielddSecurity.CapturedWordSlots211B016.W65.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B016.W65.outside
#print axioms ShielddSecurity.CapturedWordSlots211B016.W65.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B016.W65.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B016.W65.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B016.W65.sound
#print axioms ShielddSecurity.CapturedWordSlots211B016.W65.sound
