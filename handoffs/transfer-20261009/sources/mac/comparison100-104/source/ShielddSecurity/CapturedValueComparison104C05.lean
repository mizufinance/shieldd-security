import ShielddSecurity.ComparisonCertificate101
import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedFullArithmetic52
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedValueComparison104C05
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ComparisonCertificate101
def entries : List Entry := [⟨377,false,[(32564,1)],[(32566,1)],32566,32567,[⟨[(377,1),(32564,1),(200692,((p:Int)-1))],[(32567,1)]⟩,⟨[(377,((p:Int)-1)),(32564,1),(200692,1)],[(32566,4),(32567,1)]⟩]⟩,⟨378,false,[(32566,1)],[(32568,1)],32568,32569,[⟨[(378,1),(32566,1),(200692,((p:Int)-1))],[(32569,1)]⟩,⟨[(378,((p:Int)-1)),(32566,1),(200692,1)],[(32568,4),(32569,1)]⟩]⟩,⟨379,true,[(32568,1)],[(379,-1),(32570,1),(200692,1)],32570,32571,[⟨[(379,((p:Int)-1)),(32568,1)],[(32571,1)]⟩,⟨[(379,1),(32568,1)],[(32570,4),(32571,1)]⟩]⟩,⟨380,false,[(379,-1),(32570,1),(200692,1)],[(32572,1)],32572,32573,[⟨[(379,((p:Int)-1)),(380,1),(32570,1)],[(32573,1)]⟩,⟨[(379,((p:Int)-1)),(380,((p:Int)-1)),(32570,1),(200692,2)],[(32572,4),(32573,1)]⟩]⟩,⟨381,false,[(32572,1)],[(32574,1)],32574,32575,[⟨[(381,1),(32572,1),(200692,((p:Int)-1))],[(32575,1)]⟩,⟨[(381,((p:Int)-1)),(32572,1),(200692,1)],[(32574,4),(32575,1)]⟩]⟩,⟨382,false,[(32574,1)],[(32576,1)],32576,32577,[⟨[(382,1),(32574,1),(200692,((p:Int)-1))],[(32577,1)]⟩,⟨[(382,((p:Int)-1)),(32574,1),(200692,1)],[(32576,4),(32577,1)]⟩]⟩,⟨383,false,[(32576,1)],[(32578,1)],32578,32579,[⟨[(383,1),(32576,1),(200692,((p:Int)-1))],[(32579,1)]⟩,⟨[(383,((p:Int)-1)),(32576,1),(200692,1)],[(32578,4),(32579,1)]⟩]⟩,⟨384,false,[(32578,1)],[(32580,1)],32580,32581,[⟨[(384,1),(32578,1),(200692,((p:Int)-1))],[(32581,1)]⟩,⟨[(384,((p:Int)-1)),(32578,1),(200692,1)],[(32580,4),(32581,1)]⟩]⟩,⟨385,false,[(32580,1)],[(32582,1)],32582,32583,[⟨[(385,1),(32580,1),(200692,((p:Int)-1))],[(32583,1)]⟩,⟨[(385,((p:Int)-1)),(32580,1),(200692,1)],[(32582,4),(32583,1)]⟩]⟩,⟨386,false,[(32582,1)],[(32584,1)],32584,32585,[⟨[(386,1),(32582,1),(200692,((p:Int)-1))],[(32585,1)]⟩,⟨[(386,((p:Int)-1)),(32582,1),(200692,1)],[(32584,4),(32585,1)]⟩]⟩,⟨387,true,[(32584,1)],[(387,-1),(32586,1),(200692,1)],32586,32587,[⟨[(387,((p:Int)-1)),(32584,1)],[(32587,1)]⟩,⟨[(387,1),(32584,1)],[(32586,4),(32587,1)]⟩]⟩,⟨388,true,[(387,-1),(32586,1),(200692,1)],[(388,-1),(32588,1),(200692,1)],32588,32589,[⟨[(387,((p:Int)-1)),(388,((p:Int)-1)),(32586,1),(200692,1)],[(32589,1)]⟩,⟨[(387,((p:Int)-1)),(388,1),(32586,1),(200692,1)],[(32588,4),(32589,1)]⟩]⟩,⟨389,false,[(388,-1),(32588,1),(200692,1)],[(32590,1)],32590,32591,[⟨[(388,((p:Int)-1)),(389,1),(32588,1)],[(32591,1)]⟩,⟨[(388,((p:Int)-1)),(389,((p:Int)-1)),(32588,1),(200692,2)],[(32590,4),(32591,1)]⟩]⟩,⟨390,true,[(32590,1)],[(390,-1),(32592,1),(200692,1)],32592,32593,[⟨[(390,((p:Int)-1)),(32590,1)],[(32593,1)]⟩,⟨[(390,1),(32590,1)],[(32592,4),(32593,1)]⟩]⟩,⟨391,true,[(390,-1),(32592,1),(200692,1)],[(391,-1),(32594,1),(200692,1)],32594,32595,[⟨[(390,((p:Int)-1)),(391,((p:Int)-1)),(32592,1),(200692,1)],[(32595,1)]⟩,⟨[(390,((p:Int)-1)),(391,1),(32592,1),(200692,1)],[(32594,4),(32595,1)]⟩]⟩,⟨392,true,[(391,-1),(32594,1),(200692,1)],[(392,-1),(32596,1),(200692,1)],32596,32597,[⟨[(391,((p:Int)-1)),(392,((p:Int)-1)),(32594,1),(200692,1)],[(32597,1)]⟩,⟨[(391,((p:Int)-1)),(392,1),(32594,1),(200692,1)],[(32596,4),(32597,1)]⟩]⟩,⟨393,false,[(392,-1),(32596,1),(200692,1)],[(32598,1)],32598,32599,[⟨[(392,((p:Int)-1)),(393,1),(32596,1)],[(32599,1)]⟩,⟨[(392,((p:Int)-1)),(393,((p:Int)-1)),(32596,1),(200692,2)],[(32598,4),(32599,1)]⟩]⟩,⟨394,false,[(32598,1)],[(32600,1)],32600,32601,[⟨[(394,1),(32598,1),(200692,((p:Int)-1))],[(32601,1)]⟩,⟨[(394,((p:Int)-1)),(32598,1),(200692,1)],[(32600,4),(32601,1)]⟩]⟩,⟨395,true,[(32600,1)],[(395,-1),(32602,1),(200692,1)],32602,32603,[⟨[(395,((p:Int)-1)),(32600,1)],[(32603,1)]⟩,⟨[(395,1),(32600,1)],[(32602,4),(32603,1)]⟩]⟩,⟨396,true,[(395,-1),(32602,1),(200692,1)],[(396,-1),(32604,1),(200692,1)],32604,32605,[⟨[(395,((p:Int)-1)),(396,((p:Int)-1)),(32602,1),(200692,1)],[(32605,1)]⟩,⟨[(395,((p:Int)-1)),(396,1),(32602,1),(200692,1)],[(32604,4),(32605,1)]⟩]⟩,⟨397,true,[(396,-1),(32604,1),(200692,1)],[(397,-1),(32606,1),(200692,1)],32606,32607,[⟨[(396,((p:Int)-1)),(397,((p:Int)-1)),(32604,1),(200692,1)],[(32607,1)]⟩,⟨[(396,((p:Int)-1)),(397,1),(32604,1),(200692,1)],[(32606,4),(32607,1)]⟩]⟩,⟨398,false,[(397,-1),(32606,1),(200692,1)],[(32608,1)],32608,32609,[⟨[(397,((p:Int)-1)),(398,1),(32606,1)],[(32609,1)]⟩,⟨[(397,((p:Int)-1)),(398,((p:Int)-1)),(32606,1),(200692,2)],[(32608,4),(32609,1)]⟩]⟩,⟨399,false,[(32608,1)],[(32610,1)],32610,32611,[⟨[(399,1),(32608,1),(200692,((p:Int)-1))],[(32611,1)]⟩,⟨[(399,((p:Int)-1)),(32608,1),(200692,1)],[(32610,4),(32611,1)]⟩]⟩,⟨400,true,[(32610,1)],[(400,-1),(32612,1),(200692,1)],32612,32613,[⟨[(400,((p:Int)-1)),(32610,1)],[(32613,1)]⟩,⟨[(400,1),(32610,1)],[(32612,4),(32613,1)]⟩]⟩,⟨401,true,[(400,-1),(32612,1),(200692,1)],[(401,-1),(32614,1),(200692,1)],32614,32615,[⟨[(400,((p:Int)-1)),(401,((p:Int)-1)),(32612,1),(200692,1)],[(32615,1)]⟩,⟨[(400,((p:Int)-1)),(401,1),(32612,1),(200692,1)],[(32614,4),(32615,1)]⟩]⟩,⟨402,false,[(401,-1),(32614,1),(200692,1)],[(32616,1)],32616,32617,[⟨[(401,((p:Int)-1)),(402,1),(32614,1)],[(32617,1)]⟩,⟨[(401,((p:Int)-1)),(402,((p:Int)-1)),(32614,1),(200692,2)],[(32616,4),(32617,1)]⟩]⟩,⟨403,false,[(32616,1)],[(32618,1)],32618,32619,[⟨[(403,1),(32616,1),(200692,((p:Int)-1))],[(32619,1)]⟩,⟨[(403,((p:Int)-1)),(32616,1),(200692,1)],[(32618,4),(32619,1)]⟩]⟩,⟨404,true,[(32618,1)],[(404,-1),(32620,1),(200692,1)],32620,32621,[⟨[(404,((p:Int)-1)),(32618,1)],[(32621,1)]⟩,⟨[(404,1),(32618,1)],[(32620,4),(32621,1)]⟩]⟩,⟨405,true,[(404,-1),(32620,1),(200692,1)],[(405,-1),(32622,1),(200692,1)],32622,32623,[⟨[(404,((p:Int)-1)),(405,((p:Int)-1)),(32620,1),(200692,1)],[(32623,1)]⟩,⟨[(404,((p:Int)-1)),(405,1),(32620,1),(200692,1)],[(32622,4),(32623,1)]⟩]⟩,⟨406,false,[(405,-1),(32622,1),(200692,1)],[(32624,1)],32624,32625,[⟨[(405,((p:Int)-1)),(406,1),(32622,1)],[(32625,1)]⟩,⟨[(405,((p:Int)-1)),(406,((p:Int)-1)),(32622,1),(200692,2)],[(32624,4),(32625,1)]⟩]⟩,⟨407,false,[(32624,1)],[(32626,1)],32626,32627,[⟨[(407,1),(32624,1),(200692,((p:Int)-1))],[(32627,1)]⟩,⟨[(407,((p:Int)-1)),(32624,1),(200692,1)],[(32626,4),(32627,1)]⟩]⟩,⟨408,false,[(32626,1)],[(32628,1)],32628,32629,[⟨[(408,1),(32626,1),(200692,((p:Int)-1))],[(32629,1)]⟩,⟨[(408,((p:Int)-1)),(32626,1),(200692,1)],[(32628,4),(32629,1)]⟩]⟩]
def initial : Linear := [(32564,1)]
def actualRows : List Row := entries.flatMap Entry.rows
noncomputable def productionCheck : Bool := chainCheck initial entries
theorem production_checked : productionCheck=true := by decide +kernel
noncomputable def rowCheck : Bool := CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 9828 64 actualRows
theorem rows_checked : rowCheck=true := by decide +kernel
theorem output_exact : output initial entries=[(32628,1)] := by rfl
variable {F : Type} [Field F] [CharP F p]
theorem semantic (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho (output initial entries)=rawScan rho (eval rho initial) entries :=
  chain_sound rho initial entries one production_checked
    (CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 9828 64
      actualRows rows_checked (by decide) rho arithmetic)
end ShielddSecurity.CapturedValueComparison104C05

set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C05.entries
#print axioms ShielddSecurity.CapturedValueComparison104C05.entries
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C05.initial
#print axioms ShielddSecurity.CapturedValueComparison104C05.initial
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C05.actualRows
#print axioms ShielddSecurity.CapturedValueComparison104C05.actualRows
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C05.productionCheck
#print axioms ShielddSecurity.CapturedValueComparison104C05.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C05.production_checked
#print axioms ShielddSecurity.CapturedValueComparison104C05.production_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C05.rowCheck
#print axioms ShielddSecurity.CapturedValueComparison104C05.rowCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C05.rows_checked
#print axioms ShielddSecurity.CapturedValueComparison104C05.rows_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C05.output_exact
#print axioms ShielddSecurity.CapturedValueComparison104C05.output_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison104C05.semantic
#print axioms ShielddSecurity.CapturedValueComparison104C05.semantic
