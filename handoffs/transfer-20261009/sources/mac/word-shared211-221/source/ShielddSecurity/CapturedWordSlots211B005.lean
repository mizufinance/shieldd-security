import ShielddSecurity.WordHints210
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedWordSlots211B005
open WordHints210 CompilerAssertionBlock51 CompilerArithmeticTransport41
namespace W20
def slot : Slot := ⟨4467,4484,48,4411⟩
def first : Nat := 4419
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^48) (meaning : base 4411=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 182421=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^48 ∧ (n : F)=rho 4411 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W20
namespace W21
def slot : Slot := ⟨4468,4484,48,4411⟩
def first : Nat := 4419
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^48) (meaning : base 4411=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 182422=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^48 ∧ (n : F)=rho 4411 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W21
namespace W22
def slot : Slot := ⟨4599,4536,128,4534⟩
def first : Nat := 4471
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^128) (meaning : base 4534=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 182553=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^128 ∧ (n : F)=rho 4534 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W22
namespace W23
def slot : Slot := ⟨4648,4737,48,4664⟩
def first : Nat := 4600
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^48) (meaning : base 4664=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 182602=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^48 ∧ (n : F)=rho 4664 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W23
end ShielddSecurity.CapturedWordSlots211B005

set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W20.slot
#print axioms ShielddSecurity.CapturedWordSlots211B005.W20.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W20.first
#print axioms ShielddSecurity.CapturedWordSlots211B005.W20.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W20.checked
#print axioms ShielddSecurity.CapturedWordSlots211B005.W20.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W20.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B005.W20.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W20.positions
#print axioms ShielddSecurity.CapturedWordSlots211B005.W20.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W20.originals
#print axioms ShielddSecurity.CapturedWordSlots211B005.W20.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W20.outside
#print axioms ShielddSecurity.CapturedWordSlots211B005.W20.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W20.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B005.W20.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W20.sound
#print axioms ShielddSecurity.CapturedWordSlots211B005.W20.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W21.slot
#print axioms ShielddSecurity.CapturedWordSlots211B005.W21.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W21.first
#print axioms ShielddSecurity.CapturedWordSlots211B005.W21.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W21.checked
#print axioms ShielddSecurity.CapturedWordSlots211B005.W21.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W21.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B005.W21.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W21.positions
#print axioms ShielddSecurity.CapturedWordSlots211B005.W21.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W21.originals
#print axioms ShielddSecurity.CapturedWordSlots211B005.W21.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W21.outside
#print axioms ShielddSecurity.CapturedWordSlots211B005.W21.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W21.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B005.W21.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W21.sound
#print axioms ShielddSecurity.CapturedWordSlots211B005.W21.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W22.slot
#print axioms ShielddSecurity.CapturedWordSlots211B005.W22.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W22.first
#print axioms ShielddSecurity.CapturedWordSlots211B005.W22.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W22.checked
#print axioms ShielddSecurity.CapturedWordSlots211B005.W22.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W22.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B005.W22.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W22.positions
#print axioms ShielddSecurity.CapturedWordSlots211B005.W22.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W22.originals
#print axioms ShielddSecurity.CapturedWordSlots211B005.W22.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W22.outside
#print axioms ShielddSecurity.CapturedWordSlots211B005.W22.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W22.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B005.W22.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W22.sound
#print axioms ShielddSecurity.CapturedWordSlots211B005.W22.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W23.slot
#print axioms ShielddSecurity.CapturedWordSlots211B005.W23.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W23.first
#print axioms ShielddSecurity.CapturedWordSlots211B005.W23.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W23.checked
#print axioms ShielddSecurity.CapturedWordSlots211B005.W23.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W23.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B005.W23.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W23.positions
#print axioms ShielddSecurity.CapturedWordSlots211B005.W23.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W23.originals
#print axioms ShielddSecurity.CapturedWordSlots211B005.W23.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W23.outside
#print axioms ShielddSecurity.CapturedWordSlots211B005.W23.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W23.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B005.W23.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B005.W23.sound
#print axioms ShielddSecurity.CapturedWordSlots211B005.W23.sound
