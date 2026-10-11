import ShielddSecurity.WordHints210
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedWordSlots211B004
open WordHints210 CompilerAssertionBlock51 CompilerArithmeticTransport41
namespace W16
def slot : Slot := ⟨1995,1996,4,1994⟩
def first : Nat := 1991
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^4) (meaning : base 1994=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 179949=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^4 ∧ (n : F)=rho 1994 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W16
namespace W17
def slot : Slot := ⟨2250,2000,252,1995⟩
def first : Nat := 1998
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^252) (meaning : base 1995=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 180204=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^252 ∧ (n : F)=rho 1995 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W17
namespace W18
def slot : Slot := ⟨4025,3767,252,3766⟩
def first : Nat := 3773
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^252) (meaning : base 3766=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 181979=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^252 ∧ (n : F)=rho 3766 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W18
namespace W19
def slot : Slot := ⟨4418,4283,128,4281⟩
def first : Nat := 4290
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^128) (meaning : base 4281=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 182372=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^128 ∧ (n : F)=rho 4281 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W19
end ShielddSecurity.CapturedWordSlots211B004

set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W16.slot
#print axioms ShielddSecurity.CapturedWordSlots211B004.W16.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W16.first
#print axioms ShielddSecurity.CapturedWordSlots211B004.W16.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W16.checked
#print axioms ShielddSecurity.CapturedWordSlots211B004.W16.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W16.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B004.W16.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W16.positions
#print axioms ShielddSecurity.CapturedWordSlots211B004.W16.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W16.originals
#print axioms ShielddSecurity.CapturedWordSlots211B004.W16.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W16.outside
#print axioms ShielddSecurity.CapturedWordSlots211B004.W16.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W16.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B004.W16.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W16.sound
#print axioms ShielddSecurity.CapturedWordSlots211B004.W16.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W17.slot
#print axioms ShielddSecurity.CapturedWordSlots211B004.W17.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W17.first
#print axioms ShielddSecurity.CapturedWordSlots211B004.W17.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W17.checked
#print axioms ShielddSecurity.CapturedWordSlots211B004.W17.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W17.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B004.W17.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W17.positions
#print axioms ShielddSecurity.CapturedWordSlots211B004.W17.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W17.originals
#print axioms ShielddSecurity.CapturedWordSlots211B004.W17.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W17.outside
#print axioms ShielddSecurity.CapturedWordSlots211B004.W17.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W17.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B004.W17.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W17.sound
#print axioms ShielddSecurity.CapturedWordSlots211B004.W17.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W18.slot
#print axioms ShielddSecurity.CapturedWordSlots211B004.W18.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W18.first
#print axioms ShielddSecurity.CapturedWordSlots211B004.W18.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W18.checked
#print axioms ShielddSecurity.CapturedWordSlots211B004.W18.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W18.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B004.W18.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W18.positions
#print axioms ShielddSecurity.CapturedWordSlots211B004.W18.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W18.originals
#print axioms ShielddSecurity.CapturedWordSlots211B004.W18.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W18.outside
#print axioms ShielddSecurity.CapturedWordSlots211B004.W18.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W18.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B004.W18.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W18.sound
#print axioms ShielddSecurity.CapturedWordSlots211B004.W18.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W19.slot
#print axioms ShielddSecurity.CapturedWordSlots211B004.W19.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W19.first
#print axioms ShielddSecurity.CapturedWordSlots211B004.W19.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W19.checked
#print axioms ShielddSecurity.CapturedWordSlots211B004.W19.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W19.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B004.W19.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W19.positions
#print axioms ShielddSecurity.CapturedWordSlots211B004.W19.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W19.originals
#print axioms ShielddSecurity.CapturedWordSlots211B004.W19.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W19.outside
#print axioms ShielddSecurity.CapturedWordSlots211B004.W19.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W19.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B004.W19.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B004.W19.sound
#print axioms ShielddSecurity.CapturedWordSlots211B004.W19.sound
