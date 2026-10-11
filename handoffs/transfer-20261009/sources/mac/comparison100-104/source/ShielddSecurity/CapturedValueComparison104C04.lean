import ShielddSecurity.ComparisonCertificate101
import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedFullArithmetic52
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedValueComparison104C04
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ComparisonCertificate101
def entries : List Entry := [⟨345,false,[(344,-1),(32500,1),(200692,1)],[(32502,1)],32502,32503,[⟨[(344,((p:Int)-1)),(345,1),(32500,1)],[(32503,1)]⟩,⟨[(344,((p:Int)-1)),(345,((p:Int)-1)),(32500,1),(200692,2)],[(32502,4),(32503,1)]⟩]⟩,⟨346,true,[(32502,1)],[(346,-1),(32504,1),(200692,1)],32504,32505,[⟨[(346,((p:Int)-1)),(32502,1)],[(32505,1)]⟩,⟨[(346,1),(32502,1)],[(32504,4),(32505,1)]⟩]⟩,⟨347,false,[(346,-1),(32504,1),(200692,1)],[(32506,1)],32506,32507,[⟨[(346,((p:Int)-1)),(347,1),(32504,1)],[(32507,1)]⟩,⟨[(346,((p:Int)-1)),(347,((p:Int)-1)),(32504,1),(200692,2)],[(32506,4),(32507,1)]⟩]⟩,⟨348,false,[(32506,1)],[(32508,1)],32508,32509,[⟨[(348,1),(32506,1),(200692,((p:Int)-1))],[(32509,1)]⟩,⟨[(348,((p:Int)-1)),(32506,1),(200692,1)],[(32508,4),(32509,1)]⟩]⟩,⟨349,false,[(32508,1)],[(32510,1)],32510,32511,[⟨[(349,1),(32508,1),(200692,((p:Int)-1))],[(32511,1)]⟩,⟨[(349,((p:Int)-1)),(32508,1),(200692,1)],[(32510,4),(32511,1)]⟩]⟩,⟨350,false,[(32510,1)],[(32512,1)],32512,32513,[⟨[(350,1),(32510,1),(200692,((p:Int)-1))],[(32513,1)]⟩,⟨[(350,((p:Int)-1)),(32510,1),(200692,1)],[(32512,4),(32513,1)]⟩]⟩,⟨351,false,[(32512,1)],[(32514,1)],32514,32515,[⟨[(351,1),(32512,1),(200692,((p:Int)-1))],[(32515,1)]⟩,⟨[(351,((p:Int)-1)),(32512,1),(200692,1)],[(32514,4),(32515,1)]⟩]⟩,⟨352,false,[(32514,1)],[(32516,1)],32516,32517,[⟨[(352,1),(32514,1),(200692,((p:Int)-1))],[(32517,1)]⟩,⟨[(352,((p:Int)-1)),(32514,1),(200692,1)],[(32516,4),(32517,1)]⟩]⟩,⟨353,false,[(32516,1)],[(32518,1)],32518,32519,[⟨[(353,1),(32516,1),(200692,((p:Int)-1))],[(32519,1)]⟩,⟨[(353,((p:Int)-1)),(32516,1),(200692,1)],[(32518,4),(32519,1)]⟩]⟩,⟨354,false,[(32518,1)],[(32520,1)],32520,32521,[⟨[(354,1),(32518,1),(200692,((p:Int)-1))],[(32521,1)]⟩,⟨[(354,((p:Int)-1)),(32518,1),(200692,1)],[(32520,4),(32521,1)]⟩]⟩,⟨355,true,[(32520,1)],[(355,-1),(32522,1),(200692,1)],32522,32523,[⟨[(355,((p:Int)-1)),(32520,1)],[(32523,1)]⟩,⟨[(355,1),(32520,1)],[(32522,4),(32523,1)]⟩]⟩,⟨356,true,[(355,-1),(32522,1),(200692,1)],[(356,-1),(32524,1),(200692,1)],32524,32525,[⟨[(355,((p:Int)-1)),(356,((p:Int)-1)),(32522,1),(200692,1)],[(32525,1)]⟩,⟨[(355,((p:Int)-1)),(356,1),(32522,1),(200692,1)],[(32524,4),(32525,1)]⟩]⟩,⟨357,false,[(356,-1),(32524,1),(200692,1)],[(32526,1)],32526,32527,[⟨[(356,((p:Int)-1)),(357,1),(32524,1)],[(32527,1)]⟩,⟨[(356,((p:Int)-1)),(357,((p:Int)-1)),(32524,1),(200692,2)],[(32526,4),(32527,1)]⟩]⟩,⟨358,true,[(32526,1)],[(358,-1),(32528,1),(200692,1)],32528,32529,[⟨[(358,((p:Int)-1)),(32526,1)],[(32529,1)]⟩,⟨[(358,1),(32526,1)],[(32528,4),(32529,1)]⟩]⟩,⟨359,true,[(358,-1),(32528,1),(200692,1)],[(359,-1),(32530,1),(200692,1)],32530,32531,[⟨[(358,((p:Int)-1)),(359,((p:Int)-1)),(32528,1),(200692,1)],[(32531,1)]⟩,⟨[(358,((p:Int)-1)),(359,1),(32528,1),(200692,1)],[(32530,4),(32531,1)]⟩]⟩,⟨360,true,[(359,-1),(32530,1),(200692,1)],[(360,-1),(32532,1),(200692,1)],32532,32533,[⟨[(359,((p:Int)-1)),(360,((p:Int)-1)),(32530,1),(200692,1)],[(32533,1)]⟩,⟨[(359,((p:Int)-1)),(360,1),(32530,1),(200692,1)],[(32532,4),(32533,1)]⟩]⟩,⟨361,false,[(360,-1),(32532,1),(200692,1)],[(32534,1)],32534,32535,[⟨[(360,((p:Int)-1)),(361,1),(32532,1)],[(32535,1)]⟩,⟨[(360,((p:Int)-1)),(361,((p:Int)-1)),(32532,1),(200692,2)],[(32534,4),(32535,1)]⟩]⟩,⟨362,false,[(32534,1)],[(32536,1)],32536,32537,[⟨[(362,1),(32534,1),(200692,((p:Int)-1))],[(32537,1)]⟩,⟨[(362,((p:Int)-1)),(32534,1),(200692,1)],[(32536,4),(32537,1)]⟩]⟩,⟨363,false,[(32536,1)],[(32538,1)],32538,32539,[⟨[(363,1),(32536,1),(200692,((p:Int)-1))],[(32539,1)]⟩,⟨[(363,((p:Int)-1)),(32536,1),(200692,1)],[(32538,4),(32539,1)]⟩]⟩,⟨364,false,[(32538,1)],[(32540,1)],32540,32541,[⟨[(364,1),(32538,1),(200692,((p:Int)-1))],[(32541,1)]⟩,⟨[(364,((p:Int)-1)),(32538,1),(200692,1)],[(32540,4),(32541,1)]⟩]⟩,⟨365,true,[(32540,1)],[(365,-1),(32542,1),(200692,1)],32542,32543,[⟨[(365,((p:Int)-1)),(32540,1)],[(32543,1)]⟩,⟨[(365,1),(32540,1)],[(32542,4),(32543,1)]⟩]⟩,⟨366,false,[(365,-1),(32542,1),(200692,1)],[(32544,1)],32544,32545,[⟨[(365,((p:Int)-1)),(366,1),(32542,1)],[(32545,1)]⟩,⟨[(365,((p:Int)-1)),(366,((p:Int)-1)),(32542,1),(200692,2)],[(32544,4),(32545,1)]⟩]⟩,⟨367,true,[(32544,1)],[(367,-1),(32546,1),(200692,1)],32546,32547,[⟨[(367,((p:Int)-1)),(32544,1)],[(32547,1)]⟩,⟨[(367,1),(32544,1)],[(32546,4),(32547,1)]⟩]⟩,⟨368,true,[(367,-1),(32546,1),(200692,1)],[(368,-1),(32548,1),(200692,1)],32548,32549,[⟨[(367,((p:Int)-1)),(368,((p:Int)-1)),(32546,1),(200692,1)],[(32549,1)]⟩,⟨[(367,((p:Int)-1)),(368,1),(32546,1),(200692,1)],[(32548,4),(32549,1)]⟩]⟩,⟨369,false,[(368,-1),(32548,1),(200692,1)],[(32550,1)],32550,32551,[⟨[(368,((p:Int)-1)),(369,1),(32548,1)],[(32551,1)]⟩,⟨[(368,((p:Int)-1)),(369,((p:Int)-1)),(32548,1),(200692,2)],[(32550,4),(32551,1)]⟩]⟩,⟨370,false,[(32550,1)],[(32552,1)],32552,32553,[⟨[(370,1),(32550,1),(200692,((p:Int)-1))],[(32553,1)]⟩,⟨[(370,((p:Int)-1)),(32550,1),(200692,1)],[(32552,4),(32553,1)]⟩]⟩,⟨371,true,[(32552,1)],[(371,-1),(32554,1),(200692,1)],32554,32555,[⟨[(371,((p:Int)-1)),(32552,1)],[(32555,1)]⟩,⟨[(371,1),(32552,1)],[(32554,4),(32555,1)]⟩]⟩,⟨372,false,[(371,-1),(32554,1),(200692,1)],[(32556,1)],32556,32557,[⟨[(371,((p:Int)-1)),(372,1),(32554,1)],[(32557,1)]⟩,⟨[(371,((p:Int)-1)),(372,((p:Int)-1)),(32554,1),(200692,2)],[(32556,4),(32557,1)]⟩]⟩,⟨373,false,[(32556,1)],[(32558,1)],32558,32559,[⟨[(373,1),(32556,1),(200692,((p:Int)-1))],[(32559,1)]⟩,⟨[(373,((p:Int)-1)),(32556,1),(200692,1)],[(32558,4),(32559,1)]⟩]⟩,⟨374,false,[(32558,1)],[(32560,1)],32560,32561,[⟨[(374,1),(32558,1),(200692,((p:Int)-1))],[(32561,1)]⟩,⟨[(374,((p:Int)-1)),(32558,1),(200692,1)],[(32560,4),(32561,1)]⟩]⟩,⟨375,false,[(32560,1)],[(32562,1)],32562,32563,[⟨[(375,1),(32560,1),(200692,((p:Int)-1))],[(32563,1)]⟩,⟨[(375,((p:Int)-1)),(32560,1),(200692,1)],[(32562,4),(32563,1)]⟩]⟩,⟨376,false,[(32562,1)],[(32564,1)],32564,32565,[⟨[(376,1),(32562,1),(200692,((p:Int)-1))],[(32565,1)]⟩,⟨[(376,((p:Int)-1)),(32562,1),(200692,1)],[(32564,4),(32565,1)]⟩]⟩]
def initial : Linear := [(344,-1),(32500,1),(200692,1)]
def actualRows : List Row := entries.flatMap Entry.rows
noncomputable def productionCheck : Bool := chainCheck initial entries
theorem production_checked : productionCheck=true := by decide +kernel
noncomputable def rowCheck : Bool := CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 9764 64 actualRows
theorem rows_checked : rowCheck=true := by decide +kernel
theorem output_exact : output initial entries=[(32564,1)] := by rfl
variable {F : Type} [Field F] [CharP F p]
theorem semantic (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho (output initial entries)=rawScan rho (eval rho initial) entries :=
  chain_sound rho initial entries one production_checked
    (CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 9764 64
      actualRows rows_checked (by decide) rho arithmetic)
end ShielddSecurity.CapturedValueComparison104C04

set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C04.entries
#print axioms ShielddSecurity.CapturedValueComparison104C04.entries
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C04.initial
#print axioms ShielddSecurity.CapturedValueComparison104C04.initial
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C04.actualRows
#print axioms ShielddSecurity.CapturedValueComparison104C04.actualRows
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C04.productionCheck
#print axioms ShielddSecurity.CapturedValueComparison104C04.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C04.production_checked
#print axioms ShielddSecurity.CapturedValueComparison104C04.production_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C04.rowCheck
#print axioms ShielddSecurity.CapturedValueComparison104C04.rowCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C04.rows_checked
#print axioms ShielddSecurity.CapturedValueComparison104C04.rows_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C04.output_exact
#print axioms ShielddSecurity.CapturedValueComparison104C04.output_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C04.semantic
#print axioms ShielddSecurity.CapturedValueComparison104C04.semantic
