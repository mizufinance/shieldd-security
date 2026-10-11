import ShielddSecurity.CapturedCanonical217
import ShielddSecurity.CapturedValueComparison105
import ShielddSecurity.CapturedWordSlots211B000
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedCanonical216W03
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ComparisonCertificate101
abbrev Word := CapturedWordSlots211B000.W03.slot
def entries : List Entry := CapturedValueComparison105.entries
def initial : Linear := CapturedValueComparison105.initial
def actualRows : List Row := CapturedValueComparison105.actualRows
def sourceOutput : Linear := [(0,1),(470,52435875175126190479447740508185965837690552500527637822603658699938581184512),(32752,1)]
theorem production_checked : chainCheck initial entries=true := CapturedValueComparison105.production_checked
theorem columns_checked : CanonicalWord215.columns 216 entries=WordHints210.columns Word := by decide
theorem initial_checked : canonical p initial=canonical p [(copy,1),(216,-1)] := by decide
theorem terminal_checked : CapturedFullAssertions54.recipeAt 422=some (true,.linear [(0,1)] sourceOutput) := by decide
theorem terminal_bound : 422<22816 := by decide
theorem output_port : canonical p sourceOutput=canonical p (unoutline copy (output initial entries)) := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
omit [CharP F p] in
theorem maximum (rho : Nat → F) : binary ((CanonicalWord215.pairs rho 216 entries).map Prod.snd)=p-1 := by
 change binary [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,false,true,true,false,true,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,false,false,false,false,false,false,false,false,true,false,false,true,false,true,true,false,true,true,true,true,false,true,true,true,false,false,true,false,true,false,true,false,true,false,false,false,false,false,false,false,false,true,true,false,true,true,true,false,false,false,false,true,false,true,true,false,false,true,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,true,true,false,true,true,true,false,false,true,true,true,false,false,true,true,false,false,true,true,false,false,false,false,false,true,false,false,true,false,true,false,true,true,true,true,true,false,true,false,true,true,true,false,false,true,true,false,false,true,false,true,false,false,true,true,false,false,true,false,true,false,true,true,true,false,false,true,false,true,true,false,true,true,false,true,true,true,true,true,false,false,true,true,true]=p-1
 decide +kernel
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) (one : rho 0=1) :
 ∃ n : Nat,n<p ∧ (n:F)=rho 11 := by
 have linked:rho copy=rho 0 := (CapturedFullRelation58.verifier_links rho satisfied).2.2
 have arithmetic:=((CapturedFullRelation58.satisfies_split rho).mp satisfied).1
 apply CanonicalWord215.canonical_recovery rho 216 11 initial entries (linked.trans one)
   initial_checked production_checked (CapturedValueComparison105.selected_satisfies rho arithmetic)
 · rw [columns_checked]
   exact CapturedCanonical217.bits rho satisfied Word CapturedWordSlots211B000.W03.first
     CapturedWordSlots211B000.W03.bits_checked CapturedWordSlots211B000.W03.positions.2
 · exact CapturedCanonical217.accepted rho satisfied 422 terminal_bound sourceOutput
     (output initial entries) terminal_checked output_port one
 · exact maximum rho
 · rw [columns_checked]
   exact CapturedCanonical217.reconstruction rho satisfied Word CapturedWordSlots211B000.W03.positions.1
     CapturedWordSlots211B000.W03.checked
end ShielddSecurity.CapturedCanonical216W03

set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W03.Word
#print axioms ShielddSecurity.CapturedCanonical216W03.Word
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W03.entries
#print axioms ShielddSecurity.CapturedCanonical216W03.entries
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W03.initial
#print axioms ShielddSecurity.CapturedCanonical216W03.initial
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W03.actualRows
#print axioms ShielddSecurity.CapturedCanonical216W03.actualRows
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W03.sourceOutput
#print axioms ShielddSecurity.CapturedCanonical216W03.sourceOutput
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W03.production_checked
#print axioms ShielddSecurity.CapturedCanonical216W03.production_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W03.columns_checked
#print axioms ShielddSecurity.CapturedCanonical216W03.columns_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W03.initial_checked
#print axioms ShielddSecurity.CapturedCanonical216W03.initial_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W03.terminal_checked
#print axioms ShielddSecurity.CapturedCanonical216W03.terminal_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W03.terminal_bound
#print axioms ShielddSecurity.CapturedCanonical216W03.terminal_bound
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W03.output_port
#print axioms ShielddSecurity.CapturedCanonical216W03.output_port
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W03.maximum
#print axioms ShielddSecurity.CapturedCanonical216W03.maximum
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W03.sound
#print axioms ShielddSecurity.CapturedCanonical216W03.sound
