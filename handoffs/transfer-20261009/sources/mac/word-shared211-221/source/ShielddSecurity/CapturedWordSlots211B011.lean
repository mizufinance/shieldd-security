import ShielddSecurity.WordHints210
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedWordSlots211B011
open WordHints210 CompilerAssertionBlock51 CompilerArithmeticTransport41
namespace W44
def slot : Slot := ⟨11651,11612,252,11611⟩
def first : Nat := 11399
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^252) (meaning : base 11611=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 189605=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^252 ∧ (n : F)=rho 11611 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W44
namespace W45
def slot : Slot := ⟨13673,13630,252,13629⟩
def first : Nat := 13421
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^252) (meaning : base 13629=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 191627=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^252 ∧ (n : F)=rho 13629 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W45
namespace W46
def slot : Slot := ⟨14939,14892,252,14891⟩
def first : Nat := 14687
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^252) (meaning : base 14891=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 192893=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^252 ∧ (n : F)=rho 14891 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W46
namespace W47
def slot : Slot := ⟨16205,16154,252,16153⟩
def first : Nat := 15953
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^252) (meaning : base 16153=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt 194159=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^252 ∧ (n : F)=rho 16153 :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end W47
end ShielddSecurity.CapturedWordSlots211B011

set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W44.slot
#print axioms ShielddSecurity.CapturedWordSlots211B011.W44.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W44.first
#print axioms ShielddSecurity.CapturedWordSlots211B011.W44.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W44.checked
#print axioms ShielddSecurity.CapturedWordSlots211B011.W44.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W44.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B011.W44.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W44.positions
#print axioms ShielddSecurity.CapturedWordSlots211B011.W44.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W44.originals
#print axioms ShielddSecurity.CapturedWordSlots211B011.W44.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W44.outside
#print axioms ShielddSecurity.CapturedWordSlots211B011.W44.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W44.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B011.W44.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W44.sound
#print axioms ShielddSecurity.CapturedWordSlots211B011.W44.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W45.slot
#print axioms ShielddSecurity.CapturedWordSlots211B011.W45.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W45.first
#print axioms ShielddSecurity.CapturedWordSlots211B011.W45.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W45.checked
#print axioms ShielddSecurity.CapturedWordSlots211B011.W45.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W45.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B011.W45.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W45.positions
#print axioms ShielddSecurity.CapturedWordSlots211B011.W45.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W45.originals
#print axioms ShielddSecurity.CapturedWordSlots211B011.W45.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W45.outside
#print axioms ShielddSecurity.CapturedWordSlots211B011.W45.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W45.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B011.W45.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W45.sound
#print axioms ShielddSecurity.CapturedWordSlots211B011.W45.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W46.slot
#print axioms ShielddSecurity.CapturedWordSlots211B011.W46.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W46.first
#print axioms ShielddSecurity.CapturedWordSlots211B011.W46.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W46.checked
#print axioms ShielddSecurity.CapturedWordSlots211B011.W46.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W46.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B011.W46.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W46.positions
#print axioms ShielddSecurity.CapturedWordSlots211B011.W46.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W46.originals
#print axioms ShielddSecurity.CapturedWordSlots211B011.W46.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W46.outside
#print axioms ShielddSecurity.CapturedWordSlots211B011.W46.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W46.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B011.W46.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W46.sound
#print axioms ShielddSecurity.CapturedWordSlots211B011.W46.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W47.slot
#print axioms ShielddSecurity.CapturedWordSlots211B011.W47.slot
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W47.first
#print axioms ShielddSecurity.CapturedWordSlots211B011.W47.first
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W47.checked
#print axioms ShielddSecurity.CapturedWordSlots211B011.W47.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W47.bits_checked
#print axioms ShielddSecurity.CapturedWordSlots211B011.W47.bits_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W47.positions
#print axioms ShielddSecurity.CapturedWordSlots211B011.W47.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W47.originals
#print axioms ShielddSecurity.CapturedWordSlots211B011.W47.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W47.outside
#print axioms ShielddSecurity.CapturedWordSlots211B011.W47.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W47.constructor
#print axioms ShielddSecurity.CapturedWordSlots211B011.W47.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedWordSlots211B011.W47.sound
#print axioms ShielddSecurity.CapturedWordSlots211B011.W47.sound
