import ShielddSecurity.CapturedCanonical217
import ShielddSecurity.CapturedWordSlots211B012
import ShielddSecurity.CapturedCanonical216W48C00
import ShielddSecurity.CapturedCanonical216W48C01
import ShielddSecurity.CapturedCanonical216W48C02
import ShielddSecurity.CapturedCanonical216W48C03
import ShielddSecurity.CapturedCanonical216W48C04
import ShielddSecurity.CapturedCanonical216W48C05
import ShielddSecurity.CapturedCanonical216W48C06
import ShielddSecurity.CapturedCanonical216W48C07
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedCanonical216W48
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ComparisonCertificate101
abbrev Word := CapturedWordSlots211B012.W48.slot
private abbrev E0 := CapturedCanonical216W48C00.entries
private abbrev E1 := CapturedCanonical216W48C01.entries
private abbrev E2 := CapturedCanonical216W48C02.entries
private abbrev E3 := CapturedCanonical216W48C03.entries
private abbrev E4 := CapturedCanonical216W48C04.entries
private abbrev E5 := CapturedCanonical216W48C05.entries
private abbrev E6 := CapturedCanonical216W48C06.entries
private abbrev E7 := CapturedCanonical216W48C07.entries
def entries : List Entry := E0++(E1++(E2++(E3++(E4++(E5++(E6++(E7)))))))
def initial : Linear := CapturedCanonical216W48C00.initial
def sourceOutput : Linear := [(0,1),(17669,((p:Int)-1)),(178355,1)]
def actualRows : List Row := entries.flatMap Entry.rows
noncomputable def productionCheck : Bool := chainCheck initial entries
theorem production_checked : productionCheck=true := by
 have h7:= CapturedCanonical216W48C07.production_checked
 have h6 : chainCheck CapturedCanonical216W48C06.initial (E6++(E7))=true := by
  apply ComparisonComposition103.check_append
  · exact CapturedCanonical216W48C06.production_checked
  · rw [CapturedCanonical216W48C06.output_exact]
    exact h7
 have h5 : chainCheck CapturedCanonical216W48C05.initial (E5++(E6++(E7)))=true := by
  apply ComparisonComposition103.check_append
  · exact CapturedCanonical216W48C05.production_checked
  · rw [CapturedCanonical216W48C05.output_exact]
    exact h6
 have h4 : chainCheck CapturedCanonical216W48C04.initial (E4++(E5++(E6++(E7))))=true := by
  apply ComparisonComposition103.check_append
  · exact CapturedCanonical216W48C04.production_checked
  · rw [CapturedCanonical216W48C04.output_exact]
    exact h5
 have h3 : chainCheck CapturedCanonical216W48C03.initial (E3++(E4++(E5++(E6++(E7)))))=true := by
  apply ComparisonComposition103.check_append
  · exact CapturedCanonical216W48C03.production_checked
  · rw [CapturedCanonical216W48C03.output_exact]
    exact h4
 have h2 : chainCheck CapturedCanonical216W48C02.initial (E2++(E3++(E4++(E5++(E6++(E7))))))=true := by
  apply ComparisonComposition103.check_append
  · exact CapturedCanonical216W48C02.production_checked
  · rw [CapturedCanonical216W48C02.output_exact]
    exact h3
 have h1 : chainCheck CapturedCanonical216W48C01.initial (E1++(E2++(E3++(E4++(E5++(E6++(E7)))))))=true := by
  apply ComparisonComposition103.check_append
  · exact CapturedCanonical216W48C01.production_checked
  · rw [CapturedCanonical216W48C01.output_exact]
    exact h2
 have h0 : chainCheck CapturedCanonical216W48C00.initial (E0++(E1++(E2++(E3++(E4++(E5++(E6++(E7))))))))=true := by
  apply ComparisonComposition103.check_append
  · exact CapturedCanonical216W48C00.production_checked
  · rw [CapturedCanonical216W48C00.output_exact]
    exact h1
 exact h0
theorem columns_checked : CanonicalWord215.columns 17415 entries=WordHints210.columns Word := by decide
theorem initial_checked : canonical p initial=canonical p [(copy,1),(17415,-1)] := by decide
theorem terminal_checked : CapturedFullAssertions54.recipeAt 17484=some (true,.linear [(0,1)] sourceOutput) := by rfl
theorem terminal_bound : 17484<22816 := by decide
theorem output_port : canonical p sourceOutput=canonical p (unoutline copy (output initial entries)) := by decide +kernel
theorem selected : ∀ row∈entries.flatMap Entry.rows,∃ index<177954,CapturedFullArithmetic52.rowAt index=some row := by
 apply CanonicalComparisonSlices218.append
 · exact CapturedCanonical216W48C00.selected
 apply CanonicalComparisonSlices218.append
 · exact CapturedCanonical216W48C01.selected
 apply CanonicalComparisonSlices218.append
 · exact CapturedCanonical216W48C02.selected
 apply CanonicalComparisonSlices218.append
 · exact CapturedCanonical216W48C03.selected
 apply CanonicalComparisonSlices218.append
 · exact CapturedCanonical216W48C04.selected
 apply CanonicalComparisonSlices218.append
 · exact CapturedCanonical216W48C05.selected
 apply CanonicalComparisonSlices218.append
 · exact CapturedCanonical216W48C06.selected
 exact CapturedCanonical216W48C07.selected
variable {F : Type} [Field F] [CharP F p]
omit [CharP F p] in
theorem maximum (rho : Nat → F) : binary ((CanonicalWord215.pairs rho 17415 entries).map Prod.snd)=p-1 := by
 change binary [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,false,true,true,false,true,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,false,false,false,false,false,false,false,false,true,false,false,true,false,true,true,false,true,true,true,true,false,true,true,true,false,false,true,false,true,false,true,false,true,false,false,false,false,false,false,false,false,true,true,false,true,true,true,false,false,false,false,true,false,true,true,false,false,true,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,true,true,false,true,true,true,false,false,true,true,true,false,false,true,true,false,false,true,true,false,false,false,false,false,true,false,false,true,false,true,false,true,true,true,true,true,false,true,false,true,true,true,false,false,true,true,false,false,true,false,true,false,false,true,true,false,false,true,false,true,false,true,true,true,false,false,true,false,true,true,false,true,true,false,true,true,true,true,true,false,false,true,true,true]=p-1
 decide +kernel
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) (one : rho 0=1) :
 ∃ n : Nat,n<p ∧ (n:F)=rho 1743 :=
 CapturedCanonical217.sound rho satisfied one Word 17415 CapturedWordSlots211B012.W48.first initial entries
  CapturedWordSlots211B012.W48.checked CapturedWordSlots211B012.W48.positions.1
  CapturedWordSlots211B012.W48.bits_checked CapturedWordSlots211B012.W48.positions.2 columns_checked initial_checked
  production_checked selected 17484 terminal_bound sourceOutput terminal_checked output_port (maximum rho)
end ShielddSecurity.CapturedCanonical216W48

set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W48.Word
#print axioms ShielddSecurity.CapturedCanonical216W48.Word
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W48.entries
#print axioms ShielddSecurity.CapturedCanonical216W48.entries
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W48.initial
#print axioms ShielddSecurity.CapturedCanonical216W48.initial
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W48.sourceOutput
#print axioms ShielddSecurity.CapturedCanonical216W48.sourceOutput
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W48.actualRows
#print axioms ShielddSecurity.CapturedCanonical216W48.actualRows
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W48.productionCheck
#print axioms ShielddSecurity.CapturedCanonical216W48.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W48.production_checked
#print axioms ShielddSecurity.CapturedCanonical216W48.production_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W48.columns_checked
#print axioms ShielddSecurity.CapturedCanonical216W48.columns_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W48.initial_checked
#print axioms ShielddSecurity.CapturedCanonical216W48.initial_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W48.terminal_checked
#print axioms ShielddSecurity.CapturedCanonical216W48.terminal_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W48.terminal_bound
#print axioms ShielddSecurity.CapturedCanonical216W48.terminal_bound
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W48.output_port
#print axioms ShielddSecurity.CapturedCanonical216W48.output_port
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W48.selected
#print axioms ShielddSecurity.CapturedCanonical216W48.selected
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W48.maximum
#print axioms ShielddSecurity.CapturedCanonical216W48.maximum
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W48.sound
#print axioms ShielddSecurity.CapturedCanonical216W48.sound
