import ShielddSecurity.LegalWordNormalization272
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.LegalWordValueData278
open WordHints210 LegalWordNormalization272
def values : List Nat := [6,7,9,11,13,21,34,135,982,1113,1243,1374,1504,1505,1512,1513,1529,1530,1742,1743,1750,1751,1767,1768,1994,1995,3766,4281,4411,4534,4664,4789,4930,6194,6334,7608,7609,7741,7742,8256,8387,8551,9061,10083,10593,11611,13629,14891,16153,19848,19849,20937,21712]
def Avoid (slots : List (Nat × Nat)) : Prop := ∀ pair∈slots,pair.2∉values
theorem checked_avoid (slots : List (Nat × Nat))
 (checked : slots.all (fun pair => decide (pair.2∉values))=true) : Avoid slots := by
 intro pair member
 exact of_decide_eq_true ((List.all_eq_true.mp checked) pair member)
theorem append (left right : List (Nat × Nat)) (a : Avoid left) (b : Avoid right) : Avoid (left++right) := by
 intro pair member
 rcases List.mem_append.mp member with first|second
 · exact a pair first
 · exact b pair second
theorem values_checked : CapturedWordRoot213.words.all
 (fun entry => decide (Alias entry.1.value ∨ entry.1.value∈values))=true := by decide +kernel
theorem value_known (entry : Slot × Nat) (member : entry∈CapturedWordRoot213.words)
 (outside : ¬Alias entry.1.value) : entry.1.value∈values :=
 (of_decide_eq_true ((List.all_eq_true.mp values_checked) entry member)).resolve_left outside
end ShielddSecurity.LegalWordValueData278

set_option pp.all true in
#check @ShielddSecurity.LegalWordValueData278.values
#print axioms ShielddSecurity.LegalWordValueData278.values
set_option pp.all true in
#check @ShielddSecurity.LegalWordValueData278.Avoid
#print axioms ShielddSecurity.LegalWordValueData278.Avoid
set_option pp.all true in
#check @ShielddSecurity.LegalWordValueData278.checked_avoid
#print axioms ShielddSecurity.LegalWordValueData278.checked_avoid
set_option pp.all true in
#check @ShielddSecurity.LegalWordValueData278.append
#print axioms ShielddSecurity.LegalWordValueData278.append
set_option pp.all true in
#check @ShielddSecurity.LegalWordValueData278.values_checked
#print axioms ShielddSecurity.LegalWordValueData278.values_checked
set_option pp.all true in
#check @ShielddSecurity.LegalWordValueData278.value_known
#print axioms ShielddSecurity.LegalWordValueData278.value_known
