import ShielddSecurity.CapturedValueComparison102Pilot
import ShielddSecurity.CapturedValueComparison104C01
import ShielddSecurity.CapturedValueComparison104C02
import ShielddSecurity.CapturedValueComparison104C03
import ShielddSecurity.CapturedValueComparison104C04
import ShielddSecurity.CapturedValueComparison104C05
import ShielddSecurity.CapturedValueComparison104C06
import ShielddSecurity.CapturedValueComparison104C07
import ShielddSecurity.ComparisonComposition103
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedValueComparison105
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ComparisonCertificate101
private abbrev E0 := CapturedValueComparison102Pilot.entries
private abbrev E1 := CapturedValueComparison104C01.entries
private abbrev E2 := CapturedValueComparison104C02.entries
private abbrev E3 := CapturedValueComparison104C03.entries
private abbrev E4 := CapturedValueComparison104C04.entries
private abbrev E5 := CapturedValueComparison104C05.entries
private abbrev E6 := CapturedValueComparison104C06.entries
private abbrev E7 := CapturedValueComparison104C07.entries
def entries : List Entry := E0++E1++E2++E3++E4++E5++E6++E7
def initial : Linear := CapturedValueComparison102Pilot.initial
def actualRows : List Row := entries.flatMap Entry.rows
noncomputable def productionCheck : Bool := chainCheck initial entries
theorem production_checked : productionCheck=true := by
  have h7:= CapturedValueComparison104C07.production_checked
  have h6 : chainCheck CapturedValueComparison104C06.initial (E6++E7)=true := by
    apply ComparisonComposition103.check_append
    · exact CapturedValueComparison104C06.production_checked
    · rw [CapturedValueComparison104C06.output_exact]
      exact h7
  have h5 : chainCheck CapturedValueComparison104C05.initial (E5++E6++E7)=true := by
    apply ComparisonComposition103.check_append
    · exact CapturedValueComparison104C05.production_checked
    · rw [CapturedValueComparison104C05.output_exact]
      exact h6
  have h4 : chainCheck CapturedValueComparison104C04.initial (E4++E5++E6++E7)=true := by
    apply ComparisonComposition103.check_append
    · exact CapturedValueComparison104C04.production_checked
    · rw [CapturedValueComparison104C04.output_exact]
      exact h5
  have h3 : chainCheck CapturedValueComparison104C03.initial (E3++E4++E5++E6++E7)=true := by
    apply ComparisonComposition103.check_append
    · exact CapturedValueComparison104C03.production_checked
    · rw [CapturedValueComparison104C03.output_exact]
      exact h4
  have h2 : chainCheck CapturedValueComparison104C02.initial (E2++E3++E4++E5++E6++E7)=true := by
    apply ComparisonComposition103.check_append
    · exact CapturedValueComparison104C02.production_checked
    · rw [CapturedValueComparison104C02.output_exact]
      exact h3
  have h1 : chainCheck CapturedValueComparison104C01.initial (E1++E2++E3++E4++E5++E6++E7)=true := by
    apply ComparisonComposition103.check_append
    · exact CapturedValueComparison104C01.production_checked
    · rw [CapturedValueComparison104C01.output_exact]
      exact h2
  have h0 : chainCheck CapturedValueComparison102Pilot.initial (E0++E1++E2++E3++E4++E5++E6++E7)=true := by
    apply ComparisonComposition103.check_append
    · exact CapturedValueComparison102Pilot.production_checked
    · rw [CapturedValueComparison102Pilot.output_exact]
      exact h1
  exact h0
theorem output_exact : output initial entries=[(470,-1),(32752,1),(copy,1)] := by rfl
theorem actual_count : actualRows.length=508 := by decide
variable {F : Type} [Field F]
private theorem sat_append (rho : Nat → F) (left right : List Row)
    (a : Satisfies rho left) (b : Satisfies rho right) : Satisfies rho (left++right) := by
  intro row member
  rcases List.mem_append.mp member with member|member
  · exact a row member
  · exact b row member
theorem selected_satisfies (rho : Nat → F)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : Satisfies rho actualRows := by
  have s0:=CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 9508 64
    CapturedValueComparison102Pilot.actualRows CapturedValueComparison102Pilot.rows_checked (by decide) rho arithmetic
  have s1:=CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 9572 64
    CapturedValueComparison104C01.actualRows CapturedValueComparison104C01.rows_checked (by decide) rho arithmetic
  have s2:=CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 9636 64
    CapturedValueComparison104C02.actualRows CapturedValueComparison104C02.rows_checked (by decide) rho arithmetic
  have s3:=CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 9700 64
    CapturedValueComparison104C03.actualRows CapturedValueComparison104C03.rows_checked (by decide) rho arithmetic
  have s4:=CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 9764 64
    CapturedValueComparison104C04.actualRows CapturedValueComparison104C04.rows_checked (by decide) rho arithmetic
  have s5:=CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 9828 64
    CapturedValueComparison104C05.actualRows CapturedValueComparison104C05.rows_checked (by decide) rho arithmetic
  have s6:=CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 9892 64
    CapturedValueComparison104C06.actualRows CapturedValueComparison104C06.rows_checked (by decide) rho arithmetic
  have s7:=CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 9956 60
    CapturedValueComparison104C07.actualRows CapturedValueComparison104C07.rows_checked (by decide) rho arithmetic
  change Satisfies rho (CapturedValueComparison102Pilot.actualRows++CapturedValueComparison104C01.actualRows++CapturedValueComparison104C02.actualRows++CapturedValueComparison104C03.actualRows++CapturedValueComparison104C04.actualRows++CapturedValueComparison104C05.actualRows++CapturedValueComparison104C06.actualRows++CapturedValueComparison104C07.actualRows)
  apply sat_append
  · exact s0
  apply sat_append
  · exact s1
  apply sat_append
  · exact s2
  apply sat_append
  · exact s3
  apply sat_append
  · exact s4
  apply sat_append
  · exact s5
  apply sat_append
  · exact s6
  exact s7
theorem semantic [CharP F p] (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho [(470,-1),(32752,1),(copy,1)]=rawScan rho (eval rho initial) entries := by
  rw [←output_exact]
  exact chain_sound rho initial entries one production_checked (selected_satisfies rho arithmetic)
end ShielddSecurity.CapturedValueComparison105

set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison105.entries
#print axioms ShielddSecurity.CapturedValueComparison105.entries
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison105.initial
#print axioms ShielddSecurity.CapturedValueComparison105.initial
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison105.actualRows
#print axioms ShielddSecurity.CapturedValueComparison105.actualRows
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison105.productionCheck
#print axioms ShielddSecurity.CapturedValueComparison105.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison105.production_checked
#print axioms ShielddSecurity.CapturedValueComparison105.production_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison105.output_exact
#print axioms ShielddSecurity.CapturedValueComparison105.output_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison105.actual_count
#print axioms ShielddSecurity.CapturedValueComparison105.actual_count
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison105.selected_satisfies
#print axioms ShielddSecurity.CapturedValueComparison105.selected_satisfies
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison105.semantic
#print axioms ShielddSecurity.CapturedValueComparison105.semantic
