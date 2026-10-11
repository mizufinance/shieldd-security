import ShielddSecurity.ComparisonCertificate101
import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedFullArithmetic52
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedValueComparison104C03
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ComparisonCertificate101
def entries : List Entry := [⟨313,true,[(32436,1)],[(313,-1),(32438,1),(200692,1)],32438,32439,[⟨[(313,((p:Int)-1)),(32436,1)],[(32439,1)]⟩,⟨[(313,1),(32436,1)],[(32438,4),(32439,1)]⟩]⟩,⟨314,false,[(313,-1),(32438,1),(200692,1)],[(32440,1)],32440,32441,[⟨[(313,((p:Int)-1)),(314,1),(32438,1)],[(32441,1)]⟩,⟨[(313,((p:Int)-1)),(314,((p:Int)-1)),(32438,1),(200692,2)],[(32440,4),(32441,1)]⟩]⟩,⟨315,false,[(32440,1)],[(32442,1)],32442,32443,[⟨[(315,1),(32440,1),(200692,((p:Int)-1))],[(32443,1)]⟩,⟨[(315,((p:Int)-1)),(32440,1),(200692,1)],[(32442,4),(32443,1)]⟩]⟩,⟨316,false,[(32442,1)],[(32444,1)],32444,32445,[⟨[(316,1),(32442,1),(200692,((p:Int)-1))],[(32445,1)]⟩,⟨[(316,((p:Int)-1)),(32442,1),(200692,1)],[(32444,4),(32445,1)]⟩]⟩,⟨317,false,[(32444,1)],[(32446,1)],32446,32447,[⟨[(317,1),(32444,1),(200692,((p:Int)-1))],[(32447,1)]⟩,⟨[(317,((p:Int)-1)),(32444,1),(200692,1)],[(32446,4),(32447,1)]⟩]⟩,⟨318,false,[(32446,1)],[(32448,1)],32448,32449,[⟨[(318,1),(32446,1),(200692,((p:Int)-1))],[(32449,1)]⟩,⟨[(318,((p:Int)-1)),(32446,1),(200692,1)],[(32448,4),(32449,1)]⟩]⟩,⟨319,false,[(32448,1)],[(32450,1)],32450,32451,[⟨[(319,1),(32448,1),(200692,((p:Int)-1))],[(32451,1)]⟩,⟨[(319,((p:Int)-1)),(32448,1),(200692,1)],[(32450,4),(32451,1)]⟩]⟩,⟨320,false,[(32450,1)],[(32452,1)],32452,32453,[⟨[(320,1),(32450,1),(200692,((p:Int)-1))],[(32453,1)]⟩,⟨[(320,((p:Int)-1)),(32450,1),(200692,1)],[(32452,4),(32453,1)]⟩]⟩,⟨321,false,[(32452,1)],[(32454,1)],32454,32455,[⟨[(321,1),(32452,1),(200692,((p:Int)-1))],[(32455,1)]⟩,⟨[(321,((p:Int)-1)),(32452,1),(200692,1)],[(32454,4),(32455,1)]⟩]⟩,⟨322,true,[(32454,1)],[(322,-1),(32456,1),(200692,1)],32456,32457,[⟨[(322,((p:Int)-1)),(32454,1)],[(32457,1)]⟩,⟨[(322,1),(32454,1)],[(32456,4),(32457,1)]⟩]⟩,⟨323,false,[(322,-1),(32456,1),(200692,1)],[(32458,1)],32458,32459,[⟨[(322,((p:Int)-1)),(323,1),(32456,1)],[(32459,1)]⟩,⟨[(322,((p:Int)-1)),(323,((p:Int)-1)),(32456,1),(200692,2)],[(32458,4),(32459,1)]⟩]⟩,⟨324,false,[(32458,1)],[(32460,1)],32460,32461,[⟨[(324,1),(32458,1),(200692,((p:Int)-1))],[(32461,1)]⟩,⟨[(324,((p:Int)-1)),(32458,1),(200692,1)],[(32460,4),(32461,1)]⟩]⟩,⟨325,true,[(32460,1)],[(325,-1),(32462,1),(200692,1)],32462,32463,[⟨[(325,((p:Int)-1)),(32460,1)],[(32463,1)]⟩,⟨[(325,1),(32460,1)],[(32462,4),(32463,1)]⟩]⟩,⟨326,false,[(325,-1),(32462,1),(200692,1)],[(32464,1)],32464,32465,[⟨[(325,((p:Int)-1)),(326,1),(32462,1)],[(32465,1)]⟩,⟨[(325,((p:Int)-1)),(326,((p:Int)-1)),(32462,1),(200692,2)],[(32464,4),(32465,1)]⟩]⟩,⟨327,true,[(32464,1)],[(327,-1),(32466,1),(200692,1)],32466,32467,[⟨[(327,((p:Int)-1)),(32464,1)],[(32467,1)]⟩,⟨[(327,1),(32464,1)],[(32466,4),(32467,1)]⟩]⟩,⟨328,true,[(327,-1),(32466,1),(200692,1)],[(328,-1),(32468,1),(200692,1)],32468,32469,[⟨[(327,((p:Int)-1)),(328,((p:Int)-1)),(32466,1),(200692,1)],[(32469,1)]⟩,⟨[(327,((p:Int)-1)),(328,1),(32466,1),(200692,1)],[(32468,4),(32469,1)]⟩]⟩,⟨329,false,[(328,-1),(32468,1),(200692,1)],[(32470,1)],32470,32471,[⟨[(328,((p:Int)-1)),(329,1),(32468,1)],[(32471,1)]⟩,⟨[(328,((p:Int)-1)),(329,((p:Int)-1)),(32468,1),(200692,2)],[(32470,4),(32471,1)]⟩]⟩,⟨330,true,[(32470,1)],[(330,-1),(32472,1),(200692,1)],32472,32473,[⟨[(330,((p:Int)-1)),(32470,1)],[(32473,1)]⟩,⟨[(330,1),(32470,1)],[(32472,4),(32473,1)]⟩]⟩,⟨331,true,[(330,-1),(32472,1),(200692,1)],[(331,-1),(32474,1),(200692,1)],32474,32475,[⟨[(330,((p:Int)-1)),(331,((p:Int)-1)),(32472,1),(200692,1)],[(32475,1)]⟩,⟨[(330,((p:Int)-1)),(331,1),(32472,1),(200692,1)],[(32474,4),(32475,1)]⟩]⟩,⟨332,true,[(331,-1),(32474,1),(200692,1)],[(332,-1),(32476,1),(200692,1)],32476,32477,[⟨[(331,((p:Int)-1)),(332,((p:Int)-1)),(32474,1),(200692,1)],[(32477,1)]⟩,⟨[(331,((p:Int)-1)),(332,1),(32474,1),(200692,1)],[(32476,4),(32477,1)]⟩]⟩,⟨333,true,[(332,-1),(32476,1),(200692,1)],[(333,-1),(32478,1),(200692,1)],32478,32479,[⟨[(332,((p:Int)-1)),(333,((p:Int)-1)),(32476,1),(200692,1)],[(32479,1)]⟩,⟨[(332,((p:Int)-1)),(333,1),(32476,1),(200692,1)],[(32478,4),(32479,1)]⟩]⟩,⟨334,false,[(333,-1),(32478,1),(200692,1)],[(32480,1)],32480,32481,[⟨[(333,((p:Int)-1)),(334,1),(32478,1)],[(32481,1)]⟩,⟨[(333,((p:Int)-1)),(334,((p:Int)-1)),(32478,1),(200692,2)],[(32480,4),(32481,1)]⟩]⟩,⟨335,true,[(32480,1)],[(335,-1),(32482,1),(200692,1)],32482,32483,[⟨[(335,((p:Int)-1)),(32480,1)],[(32483,1)]⟩,⟨[(335,1),(32480,1)],[(32482,4),(32483,1)]⟩]⟩,⟨336,true,[(335,-1),(32482,1),(200692,1)],[(336,-1),(32484,1),(200692,1)],32484,32485,[⟨[(335,((p:Int)-1)),(336,((p:Int)-1)),(32482,1),(200692,1)],[(32485,1)]⟩,⟨[(335,((p:Int)-1)),(336,1),(32482,1),(200692,1)],[(32484,4),(32485,1)]⟩]⟩,⟨337,true,[(336,-1),(32484,1),(200692,1)],[(337,-1),(32486,1),(200692,1)],32486,32487,[⟨[(336,((p:Int)-1)),(337,((p:Int)-1)),(32484,1),(200692,1)],[(32487,1)]⟩,⟨[(336,((p:Int)-1)),(337,1),(32484,1),(200692,1)],[(32486,4),(32487,1)]⟩]⟩,⟨338,false,[(337,-1),(32486,1),(200692,1)],[(32488,1)],32488,32489,[⟨[(337,((p:Int)-1)),(338,1),(32486,1)],[(32489,1)]⟩,⟨[(337,((p:Int)-1)),(338,((p:Int)-1)),(32486,1),(200692,2)],[(32488,4),(32489,1)]⟩]⟩,⟨339,false,[(32488,1)],[(32490,1)],32490,32491,[⟨[(339,1),(32488,1),(200692,((p:Int)-1))],[(32491,1)]⟩,⟨[(339,((p:Int)-1)),(32488,1),(200692,1)],[(32490,4),(32491,1)]⟩]⟩,⟨340,true,[(32490,1)],[(340,-1),(32492,1),(200692,1)],32492,32493,[⟨[(340,((p:Int)-1)),(32490,1)],[(32493,1)]⟩,⟨[(340,1),(32490,1)],[(32492,4),(32493,1)]⟩]⟩,⟨341,false,[(340,-1),(32492,1),(200692,1)],[(32494,1)],32494,32495,[⟨[(340,((p:Int)-1)),(341,1),(32492,1)],[(32495,1)]⟩,⟨[(340,((p:Int)-1)),(341,((p:Int)-1)),(32492,1),(200692,2)],[(32494,4),(32495,1)]⟩]⟩,⟨342,true,[(32494,1)],[(342,-1),(32496,1),(200692,1)],32496,32497,[⟨[(342,((p:Int)-1)),(32494,1)],[(32497,1)]⟩,⟨[(342,1),(32494,1)],[(32496,4),(32497,1)]⟩]⟩,⟨343,false,[(342,-1),(32496,1),(200692,1)],[(32498,1)],32498,32499,[⟨[(342,((p:Int)-1)),(343,1),(32496,1)],[(32499,1)]⟩,⟨[(342,((p:Int)-1)),(343,((p:Int)-1)),(32496,1),(200692,2)],[(32498,4),(32499,1)]⟩]⟩,⟨344,true,[(32498,1)],[(344,-1),(32500,1),(200692,1)],32500,32501,[⟨[(344,((p:Int)-1)),(32498,1)],[(32501,1)]⟩,⟨[(344,1),(32498,1)],[(32500,4),(32501,1)]⟩]⟩]
def initial : Linear := [(32436,1)]
def actualRows : List Row := entries.flatMap Entry.rows
noncomputable def productionCheck : Bool := chainCheck initial entries
theorem production_checked : productionCheck=true := by decide +kernel
noncomputable def rowCheck : Bool := CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 9700 64 actualRows
theorem rows_checked : rowCheck=true := by decide +kernel
theorem output_exact : output initial entries=[(344,-1),(32500,1),(200692,1)] := by rfl
variable {F : Type} [Field F] [CharP F p]
theorem semantic (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho (output initial entries)=rawScan rho (eval rho initial) entries :=
  chain_sound rho initial entries one production_checked
    (CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 9700 64
      actualRows rows_checked (by decide) rho arithmetic)
end ShielddSecurity.CapturedValueComparison104C03

set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C03.entries
#print axioms ShielddSecurity.CapturedValueComparison104C03.entries
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C03.initial
#print axioms ShielddSecurity.CapturedValueComparison104C03.initial
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C03.actualRows
#print axioms ShielddSecurity.CapturedValueComparison104C03.actualRows
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C03.productionCheck
#print axioms ShielddSecurity.CapturedValueComparison104C03.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C03.production_checked
#print axioms ShielddSecurity.CapturedValueComparison104C03.production_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C03.rowCheck
#print axioms ShielddSecurity.CapturedValueComparison104C03.rowCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C03.rows_checked
#print axioms ShielddSecurity.CapturedValueComparison104C03.rows_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C03.output_exact
#print axioms ShielddSecurity.CapturedValueComparison104C03.output_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C03.semantic
#print axioms ShielddSecurity.CapturedValueComparison104C03.semantic
