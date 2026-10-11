import ShielddSecurity.ComparisonCertificate101
import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedFullArithmetic52
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedValueComparison104C06
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ComparisonCertificate101
def entries : List Entry := [⟨409,false,[(32628,1)],[(32630,1)],32630,32631,[⟨[(409,1),(32628,1),(200692,((p:Int)-1))],[(32631,1)]⟩,⟨[(409,((p:Int)-1)),(32628,1),(200692,1)],[(32630,4),(32631,1)]⟩]⟩,⟨410,false,[(32630,1)],[(32632,1)],32632,32633,[⟨[(410,1),(32630,1),(200692,((p:Int)-1))],[(32633,1)]⟩,⟨[(410,((p:Int)-1)),(32630,1),(200692,1)],[(32632,4),(32633,1)]⟩]⟩,⟨411,true,[(32632,1)],[(411,-1),(32634,1),(200692,1)],32634,32635,[⟨[(411,((p:Int)-1)),(32632,1)],[(32635,1)]⟩,⟨[(411,1),(32632,1)],[(32634,4),(32635,1)]⟩]⟩,⟨412,false,[(411,-1),(32634,1),(200692,1)],[(32636,1)],32636,32637,[⟨[(411,((p:Int)-1)),(412,1),(32634,1)],[(32637,1)]⟩,⟨[(411,((p:Int)-1)),(412,((p:Int)-1)),(32634,1),(200692,2)],[(32636,4),(32637,1)]⟩]⟩,⟨413,false,[(32636,1)],[(32638,1)],32638,32639,[⟨[(413,1),(32636,1),(200692,((p:Int)-1))],[(32639,1)]⟩,⟨[(413,((p:Int)-1)),(32636,1),(200692,1)],[(32638,4),(32639,1)]⟩]⟩,⟨414,true,[(32638,1)],[(414,-1),(32640,1),(200692,1)],32640,32641,[⟨[(414,((p:Int)-1)),(32638,1)],[(32641,1)]⟩,⟨[(414,1),(32638,1)],[(32640,4),(32641,1)]⟩]⟩,⟨415,false,[(414,-1),(32640,1),(200692,1)],[(32642,1)],32642,32643,[⟨[(414,((p:Int)-1)),(415,1),(32640,1)],[(32643,1)]⟩,⟨[(414,((p:Int)-1)),(415,((p:Int)-1)),(32640,1),(200692,2)],[(32642,4),(32643,1)]⟩]⟩,⟨416,true,[(32642,1)],[(416,-1),(32644,1),(200692,1)],32644,32645,[⟨[(416,((p:Int)-1)),(32642,1)],[(32645,1)]⟩,⟨[(416,1),(32642,1)],[(32644,4),(32645,1)]⟩]⟩,⟨417,false,[(416,-1),(32644,1),(200692,1)],[(32646,1)],32646,32647,[⟨[(416,((p:Int)-1)),(417,1),(32644,1)],[(32647,1)]⟩,⟨[(416,((p:Int)-1)),(417,((p:Int)-1)),(32644,1),(200692,2)],[(32646,4),(32647,1)]⟩]⟩,⟨418,true,[(32646,1)],[(418,-1),(32648,1),(200692,1)],32648,32649,[⟨[(418,((p:Int)-1)),(32646,1)],[(32649,1)]⟩,⟨[(418,1),(32646,1)],[(32648,4),(32649,1)]⟩]⟩,⟨419,true,[(418,-1),(32648,1),(200692,1)],[(419,-1),(32650,1),(200692,1)],32650,32651,[⟨[(418,((p:Int)-1)),(419,((p:Int)-1)),(32648,1),(200692,1)],[(32651,1)]⟩,⟨[(418,((p:Int)-1)),(419,1),(32648,1),(200692,1)],[(32650,4),(32651,1)]⟩]⟩,⟨420,true,[(419,-1),(32650,1),(200692,1)],[(420,-1),(32652,1),(200692,1)],32652,32653,[⟨[(419,((p:Int)-1)),(420,((p:Int)-1)),(32650,1),(200692,1)],[(32653,1)]⟩,⟨[(419,((p:Int)-1)),(420,1),(32650,1),(200692,1)],[(32652,4),(32653,1)]⟩]⟩,⟨421,true,[(420,-1),(32652,1),(200692,1)],[(421,-1),(32654,1),(200692,1)],32654,32655,[⟨[(420,((p:Int)-1)),(421,((p:Int)-1)),(32652,1),(200692,1)],[(32655,1)]⟩,⟨[(420,((p:Int)-1)),(421,1),(32652,1),(200692,1)],[(32654,4),(32655,1)]⟩]⟩,⟨422,true,[(421,-1),(32654,1),(200692,1)],[(422,-1),(32656,1),(200692,1)],32656,32657,[⟨[(421,((p:Int)-1)),(422,((p:Int)-1)),(32654,1),(200692,1)],[(32657,1)]⟩,⟨[(421,((p:Int)-1)),(422,1),(32654,1),(200692,1)],[(32656,4),(32657,1)]⟩]⟩,⟨423,false,[(422,-1),(32656,1),(200692,1)],[(32658,1)],32658,32659,[⟨[(422,((p:Int)-1)),(423,1),(32656,1)],[(32659,1)]⟩,⟨[(422,((p:Int)-1)),(423,((p:Int)-1)),(32656,1),(200692,2)],[(32658,4),(32659,1)]⟩]⟩,⟨424,true,[(32658,1)],[(424,-1),(32660,1),(200692,1)],32660,32661,[⟨[(424,((p:Int)-1)),(32658,1)],[(32661,1)]⟩,⟨[(424,1),(32658,1)],[(32660,4),(32661,1)]⟩]⟩,⟨425,false,[(424,-1),(32660,1),(200692,1)],[(32662,1)],32662,32663,[⟨[(424,((p:Int)-1)),(425,1),(32660,1)],[(32663,1)]⟩,⟨[(424,((p:Int)-1)),(425,((p:Int)-1)),(32660,1),(200692,2)],[(32662,4),(32663,1)]⟩]⟩,⟨426,true,[(32662,1)],[(426,-1),(32664,1),(200692,1)],32664,32665,[⟨[(426,((p:Int)-1)),(32662,1)],[(32665,1)]⟩,⟨[(426,1),(32662,1)],[(32664,4),(32665,1)]⟩]⟩,⟨427,true,[(426,-1),(32664,1),(200692,1)],[(427,-1),(32666,1),(200692,1)],32666,32667,[⟨[(426,((p:Int)-1)),(427,((p:Int)-1)),(32664,1),(200692,1)],[(32667,1)]⟩,⟨[(426,((p:Int)-1)),(427,1),(32664,1),(200692,1)],[(32666,4),(32667,1)]⟩]⟩,⟨428,true,[(427,-1),(32666,1),(200692,1)],[(428,-1),(32668,1),(200692,1)],32668,32669,[⟨[(427,((p:Int)-1)),(428,((p:Int)-1)),(32666,1),(200692,1)],[(32669,1)]⟩,⟨[(427,((p:Int)-1)),(428,1),(32666,1),(200692,1)],[(32668,4),(32669,1)]⟩]⟩,⟨429,false,[(428,-1),(32668,1),(200692,1)],[(32670,1)],32670,32671,[⟨[(428,((p:Int)-1)),(429,1),(32668,1)],[(32671,1)]⟩,⟨[(428,((p:Int)-1)),(429,((p:Int)-1)),(32668,1),(200692,2)],[(32670,4),(32671,1)]⟩]⟩,⟨430,false,[(32670,1)],[(32672,1)],32672,32673,[⟨[(430,1),(32670,1),(200692,((p:Int)-1))],[(32673,1)]⟩,⟨[(430,((p:Int)-1)),(32670,1),(200692,1)],[(32672,4),(32673,1)]⟩]⟩,⟨431,true,[(32672,1)],[(431,-1),(32674,1),(200692,1)],32674,32675,[⟨[(431,((p:Int)-1)),(32672,1)],[(32675,1)]⟩,⟨[(431,1),(32672,1)],[(32674,4),(32675,1)]⟩]⟩,⟨432,true,[(431,-1),(32674,1),(200692,1)],[(432,-1),(32676,1),(200692,1)],32676,32677,[⟨[(431,((p:Int)-1)),(432,((p:Int)-1)),(32674,1),(200692,1)],[(32677,1)]⟩,⟨[(431,((p:Int)-1)),(432,1),(32674,1),(200692,1)],[(32676,4),(32677,1)]⟩]⟩,⟨433,false,[(432,-1),(32676,1),(200692,1)],[(32678,1)],32678,32679,[⟨[(432,((p:Int)-1)),(433,1),(32676,1)],[(32679,1)]⟩,⟨[(432,((p:Int)-1)),(433,((p:Int)-1)),(32676,1),(200692,2)],[(32678,4),(32679,1)]⟩]⟩,⟨434,false,[(32678,1)],[(32680,1)],32680,32681,[⟨[(434,1),(32678,1),(200692,((p:Int)-1))],[(32681,1)]⟩,⟨[(434,((p:Int)-1)),(32678,1),(200692,1)],[(32680,4),(32681,1)]⟩]⟩,⟨435,true,[(32680,1)],[(435,-1),(32682,1),(200692,1)],32682,32683,[⟨[(435,((p:Int)-1)),(32680,1)],[(32683,1)]⟩,⟨[(435,1),(32680,1)],[(32682,4),(32683,1)]⟩]⟩,⟨436,false,[(435,-1),(32682,1),(200692,1)],[(32684,1)],32684,32685,[⟨[(435,((p:Int)-1)),(436,1),(32682,1)],[(32685,1)]⟩,⟨[(435,((p:Int)-1)),(436,((p:Int)-1)),(32682,1),(200692,2)],[(32684,4),(32685,1)]⟩]⟩,⟨437,true,[(32684,1)],[(437,-1),(32686,1),(200692,1)],32686,32687,[⟨[(437,((p:Int)-1)),(32684,1)],[(32687,1)]⟩,⟨[(437,1),(32684,1)],[(32686,4),(32687,1)]⟩]⟩,⟨438,false,[(437,-1),(32686,1),(200692,1)],[(32688,1)],32688,32689,[⟨[(437,((p:Int)-1)),(438,1),(32686,1)],[(32689,1)]⟩,⟨[(437,((p:Int)-1)),(438,((p:Int)-1)),(32686,1),(200692,2)],[(32688,4),(32689,1)]⟩]⟩,⟨439,false,[(32688,1)],[(32690,1)],32690,32691,[⟨[(439,1),(32688,1),(200692,((p:Int)-1))],[(32691,1)]⟩,⟨[(439,((p:Int)-1)),(32688,1),(200692,1)],[(32690,4),(32691,1)]⟩]⟩,⟨440,true,[(32690,1)],[(440,-1),(32692,1),(200692,1)],32692,32693,[⟨[(440,((p:Int)-1)),(32690,1)],[(32693,1)]⟩,⟨[(440,1),(32690,1)],[(32692,4),(32693,1)]⟩]⟩]
def initial : Linear := [(32628,1)]
def actualRows : List Row := entries.flatMap Entry.rows
noncomputable def productionCheck : Bool := chainCheck initial entries
theorem production_checked : productionCheck=true := by decide +kernel
noncomputable def rowCheck : Bool := CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 9892 64 actualRows
theorem rows_checked : rowCheck=true := by decide +kernel
theorem output_exact : output initial entries=[(440,-1),(32692,1),(200692,1)] := by rfl
variable {F : Type} [Field F] [CharP F p]
theorem semantic (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho (output initial entries)=rawScan rho (eval rho initial) entries :=
  chain_sound rho initial entries one production_checked
    (CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 9892 64
      actualRows rows_checked (by decide) rho arithmetic)
end ShielddSecurity.CapturedValueComparison104C06

set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C06.entries
#print axioms ShielddSecurity.CapturedValueComparison104C06.entries
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C06.initial
#print axioms ShielddSecurity.CapturedValueComparison104C06.initial
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C06.actualRows
#print axioms ShielddSecurity.CapturedValueComparison104C06.actualRows
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C06.productionCheck
#print axioms ShielddSecurity.CapturedValueComparison104C06.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C06.production_checked
#print axioms ShielddSecurity.CapturedValueComparison104C06.production_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C06.rowCheck
#print axioms ShielddSecurity.CapturedValueComparison104C06.rowCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C06.rows_checked
#print axioms ShielddSecurity.CapturedValueComparison104C06.rows_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C06.output_exact
#print axioms ShielddSecurity.CapturedValueComparison104C06.output_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C06.semantic
#print axioms ShielddSecurity.CapturedValueComparison104C06.semantic
