import ShielddSecurity.CanonicalWord215
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedCanonical217
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ComparisonCertificate101
variable {F : Type} [Field F] [CharP F p]
theorem bits (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (slot : WordHints210.Slot) (first : Nat)
 (checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (WordHints210.bitSlots slot first)=true)
 (positions : first+slot.width≤22816) :
 ∀ column∈WordHints210.columns slot,Square (rho column) (rho column) := by
 have truth:=((CapturedFullRelation58.satisfies_iff rho).mp satisfied).2
 intro column member
 obtain ⟨bit,known,equal⟩:=WordHints210.bit_coverage slot first column member
 obtain ⟨outlined,found⟩:=BooleanHints207.checked_slot _ _ checked bit known
 have b:=truth bit.1 (WordHints210.bit_positions slot first positions bit known) _ found
 change Square (eval rho [(bit.2,1)]) (eval rho [(bit.2,1)]) at b
 simpa only [eval,Int.cast_one,one_mul,add_zero,equal] using b
theorem reconstruction (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (slot : WordHints210.Slot) (position : slot.position<22816)
 (checked : WordHints210.checkSlot CapturedFullAssertions54.recipeAt slot=true) :
 fieldBinary ((WordHints210.columns slot).map rho)=rho slot.value := by
 have truth:=((CapturedFullRelation58.satisfies_iff rho).mp satisfied).2
 obtain ⟨outlined,found⟩:=WordHints210.checked_slot _ slot checked
 exact (WordHints210.word_truth rho slot).mp (truth slot.position position _ found)
theorem accepted (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (position : Nat) (bound : position<22816) (raw result : Linear)
 (checked : CapturedFullAssertions54.recipeAt position=some (true,.linear [(0,1)] raw))
 (port : canonical p raw=canonical p (unoutline copy result)) (one : rho 0=1) :
 eval rho result=1 := by
 have truth:=((CapturedFullRelation58.satisfies_iff rho).mp satisfied).2 position bound _ checked
 change eval rho [(0,1)]=eval rho raw at truth
 have value : eval rho raw=1 := by
   simpa only [eval,Int.cast_one,one_mul,add_zero,one] using truth.symm
 have linked:rho copy=rho 0 := (CapturedFullRelation58.verifier_links rho satisfied).2.2
 have same:=canonical_equal rho raw (unoutline copy result) port
 rw [eval_unoutline rho copy result linked] at same
 exact same.symm.trans value
omit [CharP F p] in
theorem arithmetic_rows (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) (entries : List Entry)
 (selected : ∀ row∈entries.flatMap Entry.rows,∃ index<177954,CapturedFullArithmetic52.rowAt index=some row) :
 Satisfies rho (entries.flatMap Entry.rows) := by
 have arithmetic:=((CapturedFullRelation58.satisfies_split rho).mp satisfied).1
 intro row member
 obtain ⟨index,bound,found⟩:=selected row member
 exact arithmetic index bound row found
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) (one : rho 0=1)
 (slot : WordHints210.Slot) (firstBit firstPosition : Nat) (initial : Linear) (entries : List Entry)
 (wordChecked : WordHints210.checkSlot CapturedFullAssertions54.recipeAt slot=true)
 (wordPosition : slot.position<22816)
 (bitChecked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (WordHints210.bitSlots slot firstPosition)=true)
 (bitPositions : firstPosition+slot.width≤22816)
 (columnsChecked : CanonicalWord215.columns firstBit entries=WordHints210.columns slot)
 (initialChecked : canonical p initial=canonical p [(copy,1),(firstBit,-1)])
 (chainChecked : chainCheck initial entries=true)
 (selected : ∀ row∈entries.flatMap Entry.rows,∃ index<177954,CapturedFullArithmetic52.rowAt index=some row)
 (terminalPosition : Nat) (terminalBound : terminalPosition<22816) (raw : Linear)
 (terminalChecked : CapturedFullAssertions54.recipeAt terminalPosition=some (true,.linear [(0,1)] raw))
 (outputPort : canonical p raw=canonical p (unoutline copy (output initial entries)))
 (maximum : binary ((CanonicalWord215.pairs rho firstBit entries).map Prod.snd)=p-1) :
 ∃ n : Nat,n<p ∧ (n:F)=rho slot.value := by
 have linked:rho copy=rho 0 := (CapturedFullRelation58.verifier_links rho satisfied).2.2
 have copyOne:rho copy=1 := linked.trans one
 apply CanonicalWord215.canonical_recovery rho firstBit slot.value initial entries copyOne initialChecked chainChecked
   (arithmetic_rows rho satisfied entries selected)
 · rw [columnsChecked]
   exact bits rho satisfied slot firstPosition bitChecked bitPositions
 · exact accepted rho satisfied terminalPosition terminalBound raw (output initial entries) terminalChecked outputPort one
 · exact maximum
 · rw [columnsChecked]
   exact reconstruction rho satisfied slot wordPosition wordChecked
end ShielddSecurity.CapturedCanonical217

set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical217.bits
#print axioms ShielddSecurity.CapturedCanonical217.bits
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical217.reconstruction
#print axioms ShielddSecurity.CapturedCanonical217.reconstruction
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical217.accepted
#print axioms ShielddSecurity.CapturedCanonical217.accepted
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical217.arithmetic_rows
#print axioms ShielddSecurity.CapturedCanonical217.arithmetic_rows
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical217.sound
#print axioms ShielddSecurity.CapturedCanonical217.sound
