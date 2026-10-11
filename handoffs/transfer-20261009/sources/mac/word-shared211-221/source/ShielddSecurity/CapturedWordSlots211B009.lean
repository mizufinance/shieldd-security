import ShielddSecurity.WordHints210
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedWordSlots211B009
open WordHints210 CompilerAssertionBlock51 CompilerArithmeticTransport41
namespace W36
def slot : Slot := ⟨8313,8460,48,8387⟩
def first : Nat := 8265
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^48) (meaning : base 8387=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 186267=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^48 ∧ (n : F)=rho 8387 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W36
namespace W37
def slot : Slot := ⟨8314,8460,48,8387⟩
def first : Nat := 8265
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^48) (meaning : base 8387=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 186268=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^48 ∧ (n : F)=rho 8387 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W37
namespace W38
def slot : Slot := ⟨8571,8552,252,8551⟩
def first : Nat := 8319
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^252) (meaning : base 8551=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 186525=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^252 ∧ (n : F)=rho 8551 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W38
namespace W39
def slot : Slot := ⟨9089,9062,255,9061⟩
def first : Nat := 8834
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^255) (meaning : base 9061=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 187043=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^255 ∧ (n : F)=rho 9061 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W39
end ShielddSecurity.CapturedWordSlots211B009

set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W36.slot
#print axioms ShielddSecurity.CapturedWordSlots211B009.W36.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W36.first
#print axioms ShielddSecurity.CapturedWordSlots211B009.W36.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W36.checked
#print axioms ShielddSecurity.CapturedWordSlots211B009.W36.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W36.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B009.W36.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W36.positions
#print axioms ShielddSecurity.CapturedWordSlots211B009.W36.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W36.originals
#print axioms ShielddSecurity.CapturedWordSlots211B009.W36.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W36.outside
#print axioms ShielddSecurity.CapturedWordSlots211B009.W36.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W36.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B009.W36.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W36.sound
#print axioms ShielddSecurity.CapturedWordSlots211B009.W36.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W37.slot
#print axioms ShielddSecurity.CapturedWordSlots211B009.W37.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W37.first
#print axioms ShielddSecurity.CapturedWordSlots211B009.W37.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W37.checked
#print axioms ShielddSecurity.CapturedWordSlots211B009.W37.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W37.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B009.W37.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W37.positions
#print axioms ShielddSecurity.CapturedWordSlots211B009.W37.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W37.originals
#print axioms ShielddSecurity.CapturedWordSlots211B009.W37.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W37.outside
#print axioms ShielddSecurity.CapturedWordSlots211B009.W37.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W37.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B009.W37.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W37.sound
#print axioms ShielddSecurity.CapturedWordSlots211B009.W37.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W38.slot
#print axioms ShielddSecurity.CapturedWordSlots211B009.W38.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W38.first
#print axioms ShielddSecurity.CapturedWordSlots211B009.W38.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W38.checked
#print axioms ShielddSecurity.CapturedWordSlots211B009.W38.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W38.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B009.W38.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W38.positions
#print axioms ShielddSecurity.CapturedWordSlots211B009.W38.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W38.originals
#print axioms ShielddSecurity.CapturedWordSlots211B009.W38.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W38.outside
#print axioms ShielddSecurity.CapturedWordSlots211B009.W38.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W38.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B009.W38.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W38.sound
#print axioms ShielddSecurity.CapturedWordSlots211B009.W38.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W39.slot
#print axioms ShielddSecurity.CapturedWordSlots211B009.W39.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W39.first
#print axioms ShielddSecurity.CapturedWordSlots211B009.W39.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W39.checked
#print axioms ShielddSecurity.CapturedWordSlots211B009.W39.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W39.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B009.W39.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W39.positions
#print axioms ShielddSecurity.CapturedWordSlots211B009.W39.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W39.originals
#print axioms ShielddSecurity.CapturedWordSlots211B009.W39.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W39.outside
#print axioms ShielddSecurity.CapturedWordSlots211B009.W39.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W39.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B009.W39.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B009.W39.sound
#print axioms ShielddSecurity.CapturedWordSlots211B009.W39.sound
