import ShielddSecurity.CanonicalComparisonSlices218
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedCanonical216W04C00
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ComparisonCertificate101
def entries : List Entry := [⟨472,false,[(471,-1),(200692,1)],[(32754,1)],32754,32755,[⟨[(471,((p:Int)-1)),(472,1)],[(32755,1)]⟩,⟨[(471,((p:Int)-1)),(472,((p:Int)-1)),(200692,2)],[(32754,4),(32755,1)]⟩]⟩,⟨473,false,[(32754,1)],[(32756,1)],32756,32757,[⟨[(473,1),(32754,1),(200692,((p:Int)-1))],[(32757,1)]⟩,⟨[(473,((p:Int)-1)),(32754,1),(200692,1)],[(32756,4),(32757,1)]⟩]⟩,⟨474,false,[(32756,1)],[(32758,1)],32758,32759,[⟨[(474,1),(32756,1),(200692,((p:Int)-1))],[(32759,1)]⟩,⟨[(474,((p:Int)-1)),(32756,1),(200692,1)],[(32758,4),(32759,1)]⟩]⟩,⟨475,false,[(32758,1)],[(32760,1)],32760,32761,[⟨[(475,1),(32758,1),(200692,((p:Int)-1))],[(32761,1)]⟩,⟨[(475,((p:Int)-1)),(32758,1),(200692,1)],[(32760,4),(32761,1)]⟩]⟩,⟨476,false,[(32760,1)],[(32762,1)],32762,32763,[⟨[(476,1),(32760,1),(200692,((p:Int)-1))],[(32763,1)]⟩,⟨[(476,((p:Int)-1)),(32760,1),(200692,1)],[(32762,4),(32763,1)]⟩]⟩,⟨477,false,[(32762,1)],[(32764,1)],32764,32765,[⟨[(477,1),(32762,1),(200692,((p:Int)-1))],[(32765,1)]⟩,⟨[(477,((p:Int)-1)),(32762,1),(200692,1)],[(32764,4),(32765,1)]⟩]⟩,⟨478,false,[(32764,1)],[(32766,1)],32766,32767,[⟨[(478,1),(32764,1),(200692,((p:Int)-1))],[(32767,1)]⟩,⟨[(478,((p:Int)-1)),(32764,1),(200692,1)],[(32766,4),(32767,1)]⟩]⟩,⟨479,false,[(32766,1)],[(32768,1)],32768,32769,[⟨[(479,1),(32766,1),(200692,((p:Int)-1))],[(32769,1)]⟩,⟨[(479,((p:Int)-1)),(32766,1),(200692,1)],[(32768,4),(32769,1)]⟩]⟩,⟨480,false,[(32768,1)],[(32770,1)],32770,32771,[⟨[(480,1),(32768,1),(200692,((p:Int)-1))],[(32771,1)]⟩,⟨[(480,((p:Int)-1)),(32768,1),(200692,1)],[(32770,4),(32771,1)]⟩]⟩,⟨481,false,[(32770,1)],[(32772,1)],32772,32773,[⟨[(481,1),(32770,1),(200692,((p:Int)-1))],[(32773,1)]⟩,⟨[(481,((p:Int)-1)),(32770,1),(200692,1)],[(32772,4),(32773,1)]⟩]⟩,⟨482,false,[(32772,1)],[(32774,1)],32774,32775,[⟨[(482,1),(32772,1),(200692,((p:Int)-1))],[(32775,1)]⟩,⟨[(482,((p:Int)-1)),(32772,1),(200692,1)],[(32774,4),(32775,1)]⟩]⟩,⟨483,false,[(32774,1)],[(32776,1)],32776,32777,[⟨[(483,1),(32774,1),(200692,((p:Int)-1))],[(32777,1)]⟩,⟨[(483,((p:Int)-1)),(32774,1),(200692,1)],[(32776,4),(32777,1)]⟩]⟩,⟨484,false,[(32776,1)],[(32778,1)],32778,32779,[⟨[(484,1),(32776,1),(200692,((p:Int)-1))],[(32779,1)]⟩,⟨[(484,((p:Int)-1)),(32776,1),(200692,1)],[(32778,4),(32779,1)]⟩]⟩,⟨485,false,[(32778,1)],[(32780,1)],32780,32781,[⟨[(485,1),(32778,1),(200692,((p:Int)-1))],[(32781,1)]⟩,⟨[(485,((p:Int)-1)),(32778,1),(200692,1)],[(32780,4),(32781,1)]⟩]⟩,⟨486,false,[(32780,1)],[(32782,1)],32782,32783,[⟨[(486,1),(32780,1),(200692,((p:Int)-1))],[(32783,1)]⟩,⟨[(486,((p:Int)-1)),(32780,1),(200692,1)],[(32782,4),(32783,1)]⟩]⟩,⟨487,false,[(32782,1)],[(32784,1)],32784,32785,[⟨[(487,1),(32782,1),(200692,((p:Int)-1))],[(32785,1)]⟩,⟨[(487,((p:Int)-1)),(32782,1),(200692,1)],[(32784,4),(32785,1)]⟩]⟩,⟨488,false,[(32784,1)],[(32786,1)],32786,32787,[⟨[(488,1),(32784,1),(200692,((p:Int)-1))],[(32787,1)]⟩,⟨[(488,((p:Int)-1)),(32784,1),(200692,1)],[(32786,4),(32787,1)]⟩]⟩,⟨489,false,[(32786,1)],[(32788,1)],32788,32789,[⟨[(489,1),(32786,1),(200692,((p:Int)-1))],[(32789,1)]⟩,⟨[(489,((p:Int)-1)),(32786,1),(200692,1)],[(32788,4),(32789,1)]⟩]⟩,⟨490,false,[(32788,1)],[(32790,1)],32790,32791,[⟨[(490,1),(32788,1),(200692,((p:Int)-1))],[(32791,1)]⟩,⟨[(490,((p:Int)-1)),(32788,1),(200692,1)],[(32790,4),(32791,1)]⟩]⟩,⟨491,false,[(32790,1)],[(32792,1)],32792,32793,[⟨[(491,1),(32790,1),(200692,((p:Int)-1))],[(32793,1)]⟩,⟨[(491,((p:Int)-1)),(32790,1),(200692,1)],[(32792,4),(32793,1)]⟩]⟩,⟨492,false,[(32792,1)],[(32794,1)],32794,32795,[⟨[(492,1),(32792,1),(200692,((p:Int)-1))],[(32795,1)]⟩,⟨[(492,((p:Int)-1)),(32792,1),(200692,1)],[(32794,4),(32795,1)]⟩]⟩,⟨493,false,[(32794,1)],[(32796,1)],32796,32797,[⟨[(493,1),(32794,1),(200692,((p:Int)-1))],[(32797,1)]⟩,⟨[(493,((p:Int)-1)),(32794,1),(200692,1)],[(32796,4),(32797,1)]⟩]⟩,⟨494,false,[(32796,1)],[(32798,1)],32798,32799,[⟨[(494,1),(32796,1),(200692,((p:Int)-1))],[(32799,1)]⟩,⟨[(494,((p:Int)-1)),(32796,1),(200692,1)],[(32798,4),(32799,1)]⟩]⟩,⟨495,false,[(32798,1)],[(32800,1)],32800,32801,[⟨[(495,1),(32798,1),(200692,((p:Int)-1))],[(32801,1)]⟩,⟨[(495,((p:Int)-1)),(32798,1),(200692,1)],[(32800,4),(32801,1)]⟩]⟩,⟨496,false,[(32800,1)],[(32802,1)],32802,32803,[⟨[(496,1),(32800,1),(200692,((p:Int)-1))],[(32803,1)]⟩,⟨[(496,((p:Int)-1)),(32800,1),(200692,1)],[(32802,4),(32803,1)]⟩]⟩,⟨497,false,[(32802,1)],[(32804,1)],32804,32805,[⟨[(497,1),(32802,1),(200692,((p:Int)-1))],[(32805,1)]⟩,⟨[(497,((p:Int)-1)),(32802,1),(200692,1)],[(32804,4),(32805,1)]⟩]⟩,⟨498,false,[(32804,1)],[(32806,1)],32806,32807,[⟨[(498,1),(32804,1),(200692,((p:Int)-1))],[(32807,1)]⟩,⟨[(498,((p:Int)-1)),(32804,1),(200692,1)],[(32806,4),(32807,1)]⟩]⟩,⟨499,false,[(32806,1)],[(32808,1)],32808,32809,[⟨[(499,1),(32806,1),(200692,((p:Int)-1))],[(32809,1)]⟩,⟨[(499,((p:Int)-1)),(32806,1),(200692,1)],[(32808,4),(32809,1)]⟩]⟩,⟨500,false,[(32808,1)],[(32810,1)],32810,32811,[⟨[(500,1),(32808,1),(200692,((p:Int)-1))],[(32811,1)]⟩,⟨[(500,((p:Int)-1)),(32808,1),(200692,1)],[(32810,4),(32811,1)]⟩]⟩,⟨501,false,[(32810,1)],[(32812,1)],32812,32813,[⟨[(501,1),(32810,1),(200692,((p:Int)-1))],[(32813,1)]⟩,⟨[(501,((p:Int)-1)),(32810,1),(200692,1)],[(32812,4),(32813,1)]⟩]⟩,⟨502,false,[(32812,1)],[(32814,1)],32814,32815,[⟨[(502,1),(32812,1),(200692,((p:Int)-1))],[(32815,1)]⟩,⟨[(502,((p:Int)-1)),(32812,1),(200692,1)],[(32814,4),(32815,1)]⟩]⟩,⟨503,true,[(32814,1)],[(503,-1),(32816,1),(200692,1)],32816,32817,[⟨[(503,((p:Int)-1)),(32814,1)],[(32817,1)]⟩,⟨[(503,1),(32814,1)],[(32816,4),(32817,1)]⟩]⟩]
def initial : Linear := [(471,-1),(200692,1)]
def actualRows : List Row := entries.flatMap Entry.rows
noncomputable def productionCheck : Bool := chainCheck initial entries
theorem production_checked : productionCheck=true := by decide +kernel
noncomputable def rowCheck : Bool := CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 10016 64 actualRows
theorem rows_checked : rowCheck=true := by decide +kernel
theorem output_exact : output initial entries=[(503,-1),(32816,1),(200692,1)] := by rfl
theorem selected : ∀ row∈entries.flatMap Entry.rows,∃ index<177954,CapturedFullArithmetic52.rowAt index=some row :=
 CanonicalComparisonSlices218.slice 10016 64 actualRows rows_checked (by decide)
end ShielddSecurity.CapturedCanonical216W04C00

set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W04C00.entries
#print axioms ShielddSecurity.CapturedCanonical216W04C00.entries
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W04C00.initial
#print axioms ShielddSecurity.CapturedCanonical216W04C00.initial
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W04C00.actualRows
#print axioms ShielddSecurity.CapturedCanonical216W04C00.actualRows
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W04C00.productionCheck
#print axioms ShielddSecurity.CapturedCanonical216W04C00.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W04C00.production_checked
#print axioms ShielddSecurity.CapturedCanonical216W04C00.production_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W04C00.rowCheck
#print axioms ShielddSecurity.CapturedCanonical216W04C00.rowCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W04C00.rows_checked
#print axioms ShielddSecurity.CapturedCanonical216W04C00.rows_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W04C00.output_exact
#print axioms ShielddSecurity.CapturedCanonical216W04C00.output_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W04C00.selected
#print axioms ShielddSecurity.CapturedCanonical216W04C00.selected
