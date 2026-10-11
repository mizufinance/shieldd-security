import ShielddSecurity.WordHints210
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedWordSlots211B007
open WordHints210 CompilerAssertionBlock51 CompilerArithmeticTransport41
namespace W28
def slot : Slot := ⟨6440,6335,252,6334⟩
def first : Nat := 6188
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^252) (meaning : base 6334=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 184394=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^252 ∧ (n : F)=rho 6334 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W28
namespace W29
def slot : Slot := ⟨7540,7610,64,7⟩
def first : Nat := 7476
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^64) (meaning : base 7=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 185494=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^64 ∧ (n : F)=rho 7 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W29
namespace W30
def slot : Slot := ⟨7589,7674,48,7608⟩
def first : Nat := 7541
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^48) (meaning : base 7608=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 185543=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^48 ∧ (n : F)=rho 7608 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W30
namespace W31
def slot : Slot := ⟨7607,7722,17,7609⟩
def first : Nat := 7590
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^17) (meaning : base 7609=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 185561=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^17 ∧ (n : F)=rho 7609 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W31
end ShielddSecurity.CapturedWordSlots211B007

set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W28.slot
#print axioms ShielddSecurity.CapturedWordSlots211B007.W28.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W28.first
#print axioms ShielddSecurity.CapturedWordSlots211B007.W28.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W28.checked
#print axioms ShielddSecurity.CapturedWordSlots211B007.W28.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W28.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B007.W28.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W28.positions
#print axioms ShielddSecurity.CapturedWordSlots211B007.W28.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W28.originals
#print axioms ShielddSecurity.CapturedWordSlots211B007.W28.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W28.outside
#print axioms ShielddSecurity.CapturedWordSlots211B007.W28.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W28.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B007.W28.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W28.sound
#print axioms ShielddSecurity.CapturedWordSlots211B007.W28.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W29.slot
#print axioms ShielddSecurity.CapturedWordSlots211B007.W29.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W29.first
#print axioms ShielddSecurity.CapturedWordSlots211B007.W29.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W29.checked
#print axioms ShielddSecurity.CapturedWordSlots211B007.W29.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W29.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B007.W29.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W29.positions
#print axioms ShielddSecurity.CapturedWordSlots211B007.W29.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W29.originals
#print axioms ShielddSecurity.CapturedWordSlots211B007.W29.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W29.outside
#print axioms ShielddSecurity.CapturedWordSlots211B007.W29.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W29.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B007.W29.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W29.sound
#print axioms ShielddSecurity.CapturedWordSlots211B007.W29.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W30.slot
#print axioms ShielddSecurity.CapturedWordSlots211B007.W30.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W30.first
#print axioms ShielddSecurity.CapturedWordSlots211B007.W30.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W30.checked
#print axioms ShielddSecurity.CapturedWordSlots211B007.W30.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W30.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B007.W30.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W30.positions
#print axioms ShielddSecurity.CapturedWordSlots211B007.W30.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W30.originals
#print axioms ShielddSecurity.CapturedWordSlots211B007.W30.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W30.outside
#print axioms ShielddSecurity.CapturedWordSlots211B007.W30.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W30.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B007.W30.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W30.sound
#print axioms ShielddSecurity.CapturedWordSlots211B007.W30.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W31.slot
#print axioms ShielddSecurity.CapturedWordSlots211B007.W31.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W31.first
#print axioms ShielddSecurity.CapturedWordSlots211B007.W31.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W31.checked
#print axioms ShielddSecurity.CapturedWordSlots211B007.W31.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W31.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B007.W31.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W31.positions
#print axioms ShielddSecurity.CapturedWordSlots211B007.W31.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W31.originals
#print axioms ShielddSecurity.CapturedWordSlots211B007.W31.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W31.outside
#print axioms ShielddSecurity.CapturedWordSlots211B007.W31.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W31.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B007.W31.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B007.W31.sound
#print axioms ShielddSecurity.CapturedWordSlots211B007.W31.sound
