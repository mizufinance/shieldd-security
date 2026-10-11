import ShielddSecurity.WordHints210
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedWordSlots211B006
open WordHints210 CompilerAssertionBlock51 CompilerArithmeticTransport41
namespace W24
def slot : Slot := ⟨4649,4737,48,4664⟩
def first : Nat := 4600
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^48) (meaning : base 4664=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 182603=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^48 ∧ (n : F)=rho 4664 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W24
namespace W25
def slot : Slot := ⟨4782,4791,128,4789⟩
def first : Nat := 4654
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^128) (meaning : base 4789=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 182736=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^128 ∧ (n : F)=rho 4789 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W25
namespace W26
def slot : Slot := ⟨5037,4931,252,4930⟩
def first : Nat := 4785
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^252) (meaning : base 4930=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 182991=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^252 ∧ (n : F)=rho 4930 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W26
namespace W27
def slot : Slot := ⟨6186,6196,128,6194⟩
def first : Nat := 6058
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^128) (meaning : base 6194=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 184140=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^128 ∧ (n : F)=rho 6194 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W27
end ShielddSecurity.CapturedWordSlots211B006

set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W24.slot
#print axioms ShielddSecurity.CapturedWordSlots211B006.W24.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W24.first
#print axioms ShielddSecurity.CapturedWordSlots211B006.W24.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W24.checked
#print axioms ShielddSecurity.CapturedWordSlots211B006.W24.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W24.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B006.W24.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W24.positions
#print axioms ShielddSecurity.CapturedWordSlots211B006.W24.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W24.originals
#print axioms ShielddSecurity.CapturedWordSlots211B006.W24.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W24.outside
#print axioms ShielddSecurity.CapturedWordSlots211B006.W24.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W24.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B006.W24.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W24.sound
#print axioms ShielddSecurity.CapturedWordSlots211B006.W24.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W25.slot
#print axioms ShielddSecurity.CapturedWordSlots211B006.W25.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W25.first
#print axioms ShielddSecurity.CapturedWordSlots211B006.W25.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W25.checked
#print axioms ShielddSecurity.CapturedWordSlots211B006.W25.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W25.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B006.W25.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W25.positions
#print axioms ShielddSecurity.CapturedWordSlots211B006.W25.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W25.originals
#print axioms ShielddSecurity.CapturedWordSlots211B006.W25.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W25.outside
#print axioms ShielddSecurity.CapturedWordSlots211B006.W25.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W25.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B006.W25.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W25.sound
#print axioms ShielddSecurity.CapturedWordSlots211B006.W25.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W26.slot
#print axioms ShielddSecurity.CapturedWordSlots211B006.W26.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W26.first
#print axioms ShielddSecurity.CapturedWordSlots211B006.W26.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W26.checked
#print axioms ShielddSecurity.CapturedWordSlots211B006.W26.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W26.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B006.W26.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W26.positions
#print axioms ShielddSecurity.CapturedWordSlots211B006.W26.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W26.originals
#print axioms ShielddSecurity.CapturedWordSlots211B006.W26.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W26.outside
#print axioms ShielddSecurity.CapturedWordSlots211B006.W26.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W26.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B006.W26.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W26.sound
#print axioms ShielddSecurity.CapturedWordSlots211B006.W26.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W27.slot
#print axioms ShielddSecurity.CapturedWordSlots211B006.W27.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W27.first
#print axioms ShielddSecurity.CapturedWordSlots211B006.W27.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W27.checked
#print axioms ShielddSecurity.CapturedWordSlots211B006.W27.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W27.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B006.W27.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W27.positions
#print axioms ShielddSecurity.CapturedWordSlots211B006.W27.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W27.originals
#print axioms ShielddSecurity.CapturedWordSlots211B006.W27.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W27.outside
#print axioms ShielddSecurity.CapturedWordSlots211B006.W27.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W27.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B006.W27.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B006.W27.sound
#print axioms ShielddSecurity.CapturedWordSlots211B006.W27.sound
