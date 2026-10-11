import ShielddSecurity.ComparisonCertificate101
import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedFullArithmetic52
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedValueComparison104C07
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ComparisonCertificate101
def entries : List Entry := [⟨441,true,[(440,-1),(32692,1),(200692,1)],[(441,-1),(32694,1),(200692,1)],32694,32695,[⟨[(440,((p:Int)-1)),(441,((p:Int)-1)),(32692,1),(200692,1)],[(32695,1)]⟩,⟨[(440,((p:Int)-1)),(441,1),(32692,1),(200692,1)],[(32694,4),(32695,1)]⟩]⟩,⟨442,false,[(441,-1),(32694,1),(200692,1)],[(32696,1)],32696,32697,[⟨[(441,((p:Int)-1)),(442,1),(32694,1)],[(32697,1)]⟩,⟨[(441,((p:Int)-1)),(442,((p:Int)-1)),(32694,1),(200692,2)],[(32696,4),(32697,1)]⟩]⟩,⟨443,false,[(32696,1)],[(32698,1)],32698,32699,[⟨[(443,1),(32696,1),(200692,((p:Int)-1))],[(32699,1)]⟩,⟨[(443,((p:Int)-1)),(32696,1),(200692,1)],[(32698,4),(32699,1)]⟩]⟩,⟨444,true,[(32698,1)],[(444,-1),(32700,1),(200692,1)],32700,32701,[⟨[(444,((p:Int)-1)),(32698,1)],[(32701,1)]⟩,⟨[(444,1),(32698,1)],[(32700,4),(32701,1)]⟩]⟩,⟨445,false,[(444,-1),(32700,1),(200692,1)],[(32702,1)],32702,32703,[⟨[(444,((p:Int)-1)),(445,1),(32700,1)],[(32703,1)]⟩,⟨[(444,((p:Int)-1)),(445,((p:Int)-1)),(32700,1),(200692,2)],[(32702,4),(32703,1)]⟩]⟩,⟨446,true,[(32702,1)],[(446,-1),(32704,1),(200692,1)],32704,32705,[⟨[(446,((p:Int)-1)),(32702,1)],[(32705,1)]⟩,⟨[(446,1),(32702,1)],[(32704,4),(32705,1)]⟩]⟩,⟨447,false,[(446,-1),(32704,1),(200692,1)],[(32706,1)],32706,32707,[⟨[(446,((p:Int)-1)),(447,1),(32704,1)],[(32707,1)]⟩,⟨[(446,((p:Int)-1)),(447,((p:Int)-1)),(32704,1),(200692,2)],[(32706,4),(32707,1)]⟩]⟩,⟨448,true,[(32706,1)],[(448,-1),(32708,1),(200692,1)],32708,32709,[⟨[(448,((p:Int)-1)),(32706,1)],[(32709,1)]⟩,⟨[(448,1),(32706,1)],[(32708,4),(32709,1)]⟩]⟩,⟨449,true,[(448,-1),(32708,1),(200692,1)],[(449,-1),(32710,1),(200692,1)],32710,32711,[⟨[(448,((p:Int)-1)),(449,((p:Int)-1)),(32708,1),(200692,1)],[(32711,1)]⟩,⟨[(448,((p:Int)-1)),(449,1),(32708,1),(200692,1)],[(32710,4),(32711,1)]⟩]⟩,⟨450,true,[(449,-1),(32710,1),(200692,1)],[(450,-1),(32712,1),(200692,1)],32712,32713,[⟨[(449,((p:Int)-1)),(450,((p:Int)-1)),(32710,1),(200692,1)],[(32713,1)]⟩,⟨[(449,((p:Int)-1)),(450,1),(32710,1),(200692,1)],[(32712,4),(32713,1)]⟩]⟩,⟨451,false,[(450,-1),(32712,1),(200692,1)],[(32714,1)],32714,32715,[⟨[(450,((p:Int)-1)),(451,1),(32712,1)],[(32715,1)]⟩,⟨[(450,((p:Int)-1)),(451,((p:Int)-1)),(32712,1),(200692,2)],[(32714,4),(32715,1)]⟩]⟩,⟨452,false,[(32714,1)],[(32716,1)],32716,32717,[⟨[(452,1),(32714,1),(200692,((p:Int)-1))],[(32717,1)]⟩,⟨[(452,((p:Int)-1)),(32714,1),(200692,1)],[(32716,4),(32717,1)]⟩]⟩,⟨453,true,[(32716,1)],[(453,-1),(32718,1),(200692,1)],32718,32719,[⟨[(453,((p:Int)-1)),(32716,1)],[(32719,1)]⟩,⟨[(453,1),(32716,1)],[(32718,4),(32719,1)]⟩]⟩,⟨454,false,[(453,-1),(32718,1),(200692,1)],[(32720,1)],32720,32721,[⟨[(453,((p:Int)-1)),(454,1),(32718,1)],[(32721,1)]⟩,⟨[(453,((p:Int)-1)),(454,((p:Int)-1)),(32718,1),(200692,2)],[(32720,4),(32721,1)]⟩]⟩,⟨455,true,[(32720,1)],[(455,-1),(32722,1),(200692,1)],32722,32723,[⟨[(455,((p:Int)-1)),(32720,1)],[(32723,1)]⟩,⟨[(455,1),(32720,1)],[(32722,4),(32723,1)]⟩]⟩,⟨456,true,[(455,-1),(32722,1),(200692,1)],[(456,-1),(32724,1),(200692,1)],32724,32725,[⟨[(455,((p:Int)-1)),(456,((p:Int)-1)),(32722,1),(200692,1)],[(32725,1)]⟩,⟨[(455,((p:Int)-1)),(456,1),(32722,1),(200692,1)],[(32724,4),(32725,1)]⟩]⟩,⟨457,false,[(456,-1),(32724,1),(200692,1)],[(32726,1)],32726,32727,[⟨[(456,((p:Int)-1)),(457,1),(32724,1)],[(32727,1)]⟩,⟨[(456,((p:Int)-1)),(457,((p:Int)-1)),(32724,1),(200692,2)],[(32726,4),(32727,1)]⟩]⟩,⟨458,true,[(32726,1)],[(458,-1),(32728,1),(200692,1)],32728,32729,[⟨[(458,((p:Int)-1)),(32726,1)],[(32729,1)]⟩,⟨[(458,1),(32726,1)],[(32728,4),(32729,1)]⟩]⟩,⟨459,true,[(458,-1),(32728,1),(200692,1)],[(459,-1),(32730,1),(200692,1)],32730,32731,[⟨[(458,((p:Int)-1)),(459,((p:Int)-1)),(32728,1),(200692,1)],[(32731,1)]⟩,⟨[(458,((p:Int)-1)),(459,1),(32728,1),(200692,1)],[(32730,4),(32731,1)]⟩]⟩,⟨460,false,[(459,-1),(32730,1),(200692,1)],[(32732,1)],32732,32733,[⟨[(459,((p:Int)-1)),(460,1),(32730,1)],[(32733,1)]⟩,⟨[(459,((p:Int)-1)),(460,((p:Int)-1)),(32730,1),(200692,2)],[(32732,4),(32733,1)]⟩]⟩,⟨461,true,[(32732,1)],[(461,-1),(32734,1),(200692,1)],32734,32735,[⟨[(461,((p:Int)-1)),(32732,1)],[(32735,1)]⟩,⟨[(461,1),(32732,1)],[(32734,4),(32735,1)]⟩]⟩,⟨462,true,[(461,-1),(32734,1),(200692,1)],[(462,-1),(32736,1),(200692,1)],32736,32737,[⟨[(461,((p:Int)-1)),(462,((p:Int)-1)),(32734,1),(200692,1)],[(32737,1)]⟩,⟨[(461,((p:Int)-1)),(462,1),(32734,1),(200692,1)],[(32736,4),(32737,1)]⟩]⟩,⟨463,true,[(462,-1),(32736,1),(200692,1)],[(463,-1),(32738,1),(200692,1)],32738,32739,[⟨[(462,((p:Int)-1)),(463,((p:Int)-1)),(32736,1),(200692,1)],[(32739,1)]⟩,⟨[(462,((p:Int)-1)),(463,1),(32736,1),(200692,1)],[(32738,4),(32739,1)]⟩]⟩,⟨464,true,[(463,-1),(32738,1),(200692,1)],[(464,-1),(32740,1),(200692,1)],32740,32741,[⟨[(463,((p:Int)-1)),(464,((p:Int)-1)),(32738,1),(200692,1)],[(32741,1)]⟩,⟨[(463,((p:Int)-1)),(464,1),(32738,1),(200692,1)],[(32740,4),(32741,1)]⟩]⟩,⟨465,true,[(464,-1),(32740,1),(200692,1)],[(465,-1),(32742,1),(200692,1)],32742,32743,[⟨[(464,((p:Int)-1)),(465,((p:Int)-1)),(32740,1),(200692,1)],[(32743,1)]⟩,⟨[(464,((p:Int)-1)),(465,1),(32740,1),(200692,1)],[(32742,4),(32743,1)]⟩]⟩,⟨466,false,[(465,-1),(32742,1),(200692,1)],[(32744,1)],32744,32745,[⟨[(465,((p:Int)-1)),(466,1),(32742,1)],[(32745,1)]⟩,⟨[(465,((p:Int)-1)),(466,((p:Int)-1)),(32742,1),(200692,2)],[(32744,4),(32745,1)]⟩]⟩,⟨467,false,[(32744,1)],[(32746,1)],32746,32747,[⟨[(467,1),(32744,1),(200692,((p:Int)-1))],[(32747,1)]⟩,⟨[(467,((p:Int)-1)),(32744,1),(200692,1)],[(32746,4),(32747,1)]⟩]⟩,⟨468,true,[(32746,1)],[(468,-1),(32748,1),(200692,1)],32748,32749,[⟨[(468,((p:Int)-1)),(32746,1)],[(32749,1)]⟩,⟨[(468,1),(32746,1)],[(32748,4),(32749,1)]⟩]⟩,⟨469,true,[(468,-1),(32748,1),(200692,1)],[(469,-1),(32750,1),(200692,1)],32750,32751,[⟨[(468,((p:Int)-1)),(469,((p:Int)-1)),(32748,1),(200692,1)],[(32751,1)]⟩,⟨[(468,((p:Int)-1)),(469,1),(32748,1),(200692,1)],[(32750,4),(32751,1)]⟩]⟩,⟨470,true,[(469,-1),(32750,1),(200692,1)],[(470,-1),(32752,1),(200692,1)],32752,32753,[⟨[(469,((p:Int)-1)),(470,((p:Int)-1)),(32750,1),(200692,1)],[(32753,1)]⟩,⟨[(469,((p:Int)-1)),(470,1),(32750,1),(200692,1)],[(32752,4),(32753,1)]⟩]⟩]
def initial : Linear := [(440,-1),(32692,1),(200692,1)]
def actualRows : List Row := entries.flatMap Entry.rows
noncomputable def productionCheck : Bool := chainCheck initial entries
theorem production_checked : productionCheck=true := by decide +kernel
noncomputable def rowCheck : Bool := CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 9956 60 actualRows
theorem rows_checked : rowCheck=true := by decide +kernel
theorem output_exact : output initial entries=[(470,-1),(32752,1),(200692,1)] := by rfl
variable {F : Type} [Field F] [CharP F p]
theorem semantic (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho (output initial entries)=rawScan rho (eval rho initial) entries :=
  chain_sound rho initial entries one production_checked
    (CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 9956 60
      actualRows rows_checked (by decide) rho arithmetic)
end ShielddSecurity.CapturedValueComparison104C07

set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C07.entries
#print axioms ShielddSecurity.CapturedValueComparison104C07.entries
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C07.initial
#print axioms ShielddSecurity.CapturedValueComparison104C07.initial
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C07.actualRows
#print axioms ShielddSecurity.CapturedValueComparison104C07.actualRows
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C07.productionCheck
#print axioms ShielddSecurity.CapturedValueComparison104C07.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C07.production_checked
#print axioms ShielddSecurity.CapturedValueComparison104C07.production_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C07.rowCheck
#print axioms ShielddSecurity.CapturedValueComparison104C07.rowCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C07.rows_checked
#print axioms ShielddSecurity.CapturedValueComparison104C07.rows_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C07.output_exact
#print axioms ShielddSecurity.CapturedValueComparison104C07.output_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C07.semantic
#print axioms ShielddSecurity.CapturedValueComparison104C07.semantic
