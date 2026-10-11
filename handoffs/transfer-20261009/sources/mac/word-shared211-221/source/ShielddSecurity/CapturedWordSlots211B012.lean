import ShielddSecurity.WordHints210
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedWordSlots211B012
open WordHints210 CompilerAssertionBlock51 CompilerArithmeticTransport41
namespace W48
def slot : Slot := ⟨17482,17415,255,1743⟩
def first : Nat := 17227
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^255) (meaning : base 1743=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 195436=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^255 ∧ (n : F)=rho 1743 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W48
namespace W49
def slot : Slot := ⟨17740,17670,255,1742⟩
def first : Nat := 17485
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^255) (meaning : base 1742=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 195694=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^255 ∧ (n : F)=rho 1742 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W49
namespace W50
def slot : Slot := ⟨17998,17925,255,1751⟩
def first : Nat := 17743
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^255) (meaning : base 1751=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 195952=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^255 ∧ (n : F)=rho 1751 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W50
namespace W51
def slot : Slot := ⟨18256,18180,255,1750⟩
def first : Nat := 18001
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^255) (meaning : base 1750=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 196210=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^255 ∧ (n : F)=rho 1750 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W51
end ShielddSecurity.CapturedWordSlots211B012

set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W48.slot
#print axioms ShielddSecurity.CapturedWordSlots211B012.W48.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W48.first
#print axioms ShielddSecurity.CapturedWordSlots211B012.W48.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W48.checked
#print axioms ShielddSecurity.CapturedWordSlots211B012.W48.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W48.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B012.W48.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W48.positions
#print axioms ShielddSecurity.CapturedWordSlots211B012.W48.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W48.originals
#print axioms ShielddSecurity.CapturedWordSlots211B012.W48.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W48.outside
#print axioms ShielddSecurity.CapturedWordSlots211B012.W48.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W48.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B012.W48.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W48.sound
#print axioms ShielddSecurity.CapturedWordSlots211B012.W48.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W49.slot
#print axioms ShielddSecurity.CapturedWordSlots211B012.W49.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W49.first
#print axioms ShielddSecurity.CapturedWordSlots211B012.W49.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W49.checked
#print axioms ShielddSecurity.CapturedWordSlots211B012.W49.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W49.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B012.W49.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W49.positions
#print axioms ShielddSecurity.CapturedWordSlots211B012.W49.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W49.originals
#print axioms ShielddSecurity.CapturedWordSlots211B012.W49.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W49.outside
#print axioms ShielddSecurity.CapturedWordSlots211B012.W49.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W49.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B012.W49.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W49.sound
#print axioms ShielddSecurity.CapturedWordSlots211B012.W49.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W50.slot
#print axioms ShielddSecurity.CapturedWordSlots211B012.W50.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W50.first
#print axioms ShielddSecurity.CapturedWordSlots211B012.W50.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W50.checked
#print axioms ShielddSecurity.CapturedWordSlots211B012.W50.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W50.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B012.W50.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W50.positions
#print axioms ShielddSecurity.CapturedWordSlots211B012.W50.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W50.originals
#print axioms ShielddSecurity.CapturedWordSlots211B012.W50.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W50.outside
#print axioms ShielddSecurity.CapturedWordSlots211B012.W50.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W50.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B012.W50.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W50.sound
#print axioms ShielddSecurity.CapturedWordSlots211B012.W50.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W51.slot
#print axioms ShielddSecurity.CapturedWordSlots211B012.W51.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W51.first
#print axioms ShielddSecurity.CapturedWordSlots211B012.W51.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W51.checked
#print axioms ShielddSecurity.CapturedWordSlots211B012.W51.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W51.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B012.W51.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W51.positions
#print axioms ShielddSecurity.CapturedWordSlots211B012.W51.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W51.originals
#print axioms ShielddSecurity.CapturedWordSlots211B012.W51.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W51.outside
#print axioms ShielddSecurity.CapturedWordSlots211B012.W51.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W51.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B012.W51.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B012.W51.sound
#print axioms ShielddSecurity.CapturedWordSlots211B012.W51.sound
