import ShielddSecurity.WordFlagCompatibility250
import ShielddSecurity.SharedWordWitness221
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedWordCompatibility251
open WordFlagCompatibility250 SharedWordFlags220
def exceptions : List (Nat × Nat) := [(9059,9061),(10591,10593),(20935,20937)]
theorem checked : check SharedWordWitness221.wordSlots exceptions=true := by decide
theorem low_agree (numbers : Nat → Nat)
 (first : numbers 9059%2=numbers 9061%2)
 (second : numbers 10591%2=numbers 10593%2)
 (third : numbers 20935%2=numbers 20937%2) : LowAgree exceptions numbers := by
 intro pair member
 simp only [exceptions,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl <;>
   simp only [bitAt,Nat.pow_zero,Nat.div_one] <;>
   first | exact congrArg (fun x : Nat => decide (x=1)) first
         | exact congrArg (fun x : Nat => decide (x=1)) second
         | exact congrArg (fun x : Nat => decide (x=1)) third
theorem coherent (numbers : Nat → Nat)
 (first : numbers 9059%2=numbers 9061%2)
 (second : numbers 10591%2=numbers 10593%2)
 (third : numbers 20935%2=numbers 20937%2) :
 Coherent (assignments SharedWordWitness221.wordSlots numbers) :=
 WordFlagCompatibility250.coherent _ _ numbers checked (low_agree numbers first second third)
end ShielddSecurity.CapturedWordCompatibility251

set_option pp.all true in
#check @ShielddSecurity.CapturedWordCompatibility251.exceptions
#print axioms ShielddSecurity.CapturedWordCompatibility251.exceptions
set_option pp.all true in
#check @ShielddSecurity.CapturedWordCompatibility251.checked
#print axioms ShielddSecurity.CapturedWordCompatibility251.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedWordCompatibility251.low_agree
#print axioms ShielddSecurity.CapturedWordCompatibility251.low_agree
set_option pp.all true in
#check @ShielddSecurity.CapturedWordCompatibility251.coherent
#print axioms ShielddSecurity.CapturedWordCompatibility251.coherent
