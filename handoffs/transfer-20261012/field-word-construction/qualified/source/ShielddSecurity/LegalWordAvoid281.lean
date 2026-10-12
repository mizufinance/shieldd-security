import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.LegalWordAvoid281
def values : List Nat := [6,7,9,11,13,21,34,135,982,1113,1243,1374,1504,1505,1512,1513,1529,1530,1742,1743,1750,1751,1767,1768,1994,1995,3766,4281,4411,4534,4664,4789,4930,6194,6334,7608,7609,7741,7742,8256,8387,8551,9061,10083,10593,11611,13629,14891,16153,19848,19849,20937,21712]
def Avoid (slots : List (Nat × Nat)) : Prop := ∀ pair∈slots,pair.2∉values
theorem checked_avoid (slots : List (Nat × Nat)) (lo hi : Nat) (near : List Nat)
 (bounds : slots.all (fun pair => decide (lo≤pair.2 ∧ pair.2≤hi))=true)
 (localCheck : slots.all (fun pair => decide (pair.2∉near))=true)
 (classification : values.all (fun value => decide (value<lo ∨ hi<value ∨ value∈near))=true) : Avoid slots := by
 intro pair member forbidden
 have inside := of_decide_eq_true ((List.all_eq_true.mp bounds) pair member)
 have outside := of_decide_eq_true ((List.all_eq_true.mp localCheck) pair member)
 have classified := of_decide_eq_true ((List.all_eq_true.mp classification) pair.2 forbidden)
 rcases classified with early|late|present
 · omega
 · omega
 · exact outside present
end ShielddSecurity.LegalWordAvoid281

set_option pp.all true in
#check @ShielddSecurity.LegalWordAvoid281.values
#print axioms ShielddSecurity.LegalWordAvoid281.values
set_option pp.all true in
#check @ShielddSecurity.LegalWordAvoid281.Avoid
#print axioms ShielddSecurity.LegalWordAvoid281.Avoid
set_option pp.all true in
#check @ShielddSecurity.LegalWordAvoid281.checked_avoid
#print axioms ShielddSecurity.LegalWordAvoid281.checked_avoid
