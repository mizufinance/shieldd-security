import ShielddSecurity.ComparisonCertificate101
import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedFullArithmetic52
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedValueComparison102Pilot
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ComparisonCertificate101
def entries : List Entry := [⟨217,false,[(216,-1),(200692,1)],[(32246,1)],32246,32247,[⟨[(216,((p:Int)-1)),(217,1)],[(32247,1)]⟩,⟨[(216,((p:Int)-1)),(217,((p:Int)-1)),(200692,2)],[(32246,4),(32247,1)]⟩]⟩,⟨218,false,[(32246,1)],[(32248,1)],32248,32249,[⟨[(218,1),(32246,1),(200692,((p:Int)-1))],[(32249,1)]⟩,⟨[(218,((p:Int)-1)),(32246,1),(200692,1)],[(32248,4),(32249,1)]⟩]⟩,⟨219,false,[(32248,1)],[(32250,1)],32250,32251,[⟨[(219,1),(32248,1),(200692,((p:Int)-1))],[(32251,1)]⟩,⟨[(219,((p:Int)-1)),(32248,1),(200692,1)],[(32250,4),(32251,1)]⟩]⟩,⟨220,false,[(32250,1)],[(32252,1)],32252,32253,[⟨[(220,1),(32250,1),(200692,((p:Int)-1))],[(32253,1)]⟩,⟨[(220,((p:Int)-1)),(32250,1),(200692,1)],[(32252,4),(32253,1)]⟩]⟩,⟨221,false,[(32252,1)],[(32254,1)],32254,32255,[⟨[(221,1),(32252,1),(200692,((p:Int)-1))],[(32255,1)]⟩,⟨[(221,((p:Int)-1)),(32252,1),(200692,1)],[(32254,4),(32255,1)]⟩]⟩,⟨222,false,[(32254,1)],[(32256,1)],32256,32257,[⟨[(222,1),(32254,1),(200692,((p:Int)-1))],[(32257,1)]⟩,⟨[(222,((p:Int)-1)),(32254,1),(200692,1)],[(32256,4),(32257,1)]⟩]⟩,⟨223,false,[(32256,1)],[(32258,1)],32258,32259,[⟨[(223,1),(32256,1),(200692,((p:Int)-1))],[(32259,1)]⟩,⟨[(223,((p:Int)-1)),(32256,1),(200692,1)],[(32258,4),(32259,1)]⟩]⟩,⟨224,false,[(32258,1)],[(32260,1)],32260,32261,[⟨[(224,1),(32258,1),(200692,((p:Int)-1))],[(32261,1)]⟩,⟨[(224,((p:Int)-1)),(32258,1),(200692,1)],[(32260,4),(32261,1)]⟩]⟩,⟨225,false,[(32260,1)],[(32262,1)],32262,32263,[⟨[(225,1),(32260,1),(200692,((p:Int)-1))],[(32263,1)]⟩,⟨[(225,((p:Int)-1)),(32260,1),(200692,1)],[(32262,4),(32263,1)]⟩]⟩,⟨226,false,[(32262,1)],[(32264,1)],32264,32265,[⟨[(226,1),(32262,1),(200692,((p:Int)-1))],[(32265,1)]⟩,⟨[(226,((p:Int)-1)),(32262,1),(200692,1)],[(32264,4),(32265,1)]⟩]⟩,⟨227,false,[(32264,1)],[(32266,1)],32266,32267,[⟨[(227,1),(32264,1),(200692,((p:Int)-1))],[(32267,1)]⟩,⟨[(227,((p:Int)-1)),(32264,1),(200692,1)],[(32266,4),(32267,1)]⟩]⟩,⟨228,false,[(32266,1)],[(32268,1)],32268,32269,[⟨[(228,1),(32266,1),(200692,((p:Int)-1))],[(32269,1)]⟩,⟨[(228,((p:Int)-1)),(32266,1),(200692,1)],[(32268,4),(32269,1)]⟩]⟩,⟨229,false,[(32268,1)],[(32270,1)],32270,32271,[⟨[(229,1),(32268,1),(200692,((p:Int)-1))],[(32271,1)]⟩,⟨[(229,((p:Int)-1)),(32268,1),(200692,1)],[(32270,4),(32271,1)]⟩]⟩,⟨230,false,[(32270,1)],[(32272,1)],32272,32273,[⟨[(230,1),(32270,1),(200692,((p:Int)-1))],[(32273,1)]⟩,⟨[(230,((p:Int)-1)),(32270,1),(200692,1)],[(32272,4),(32273,1)]⟩]⟩,⟨231,false,[(32272,1)],[(32274,1)],32274,32275,[⟨[(231,1),(32272,1),(200692,((p:Int)-1))],[(32275,1)]⟩,⟨[(231,((p:Int)-1)),(32272,1),(200692,1)],[(32274,4),(32275,1)]⟩]⟩,⟨232,false,[(32274,1)],[(32276,1)],32276,32277,[⟨[(232,1),(32274,1),(200692,((p:Int)-1))],[(32277,1)]⟩,⟨[(232,((p:Int)-1)),(32274,1),(200692,1)],[(32276,4),(32277,1)]⟩]⟩,⟨233,false,[(32276,1)],[(32278,1)],32278,32279,[⟨[(233,1),(32276,1),(200692,((p:Int)-1))],[(32279,1)]⟩,⟨[(233,((p:Int)-1)),(32276,1),(200692,1)],[(32278,4),(32279,1)]⟩]⟩,⟨234,false,[(32278,1)],[(32280,1)],32280,32281,[⟨[(234,1),(32278,1),(200692,((p:Int)-1))],[(32281,1)]⟩,⟨[(234,((p:Int)-1)),(32278,1),(200692,1)],[(32280,4),(32281,1)]⟩]⟩,⟨235,false,[(32280,1)],[(32282,1)],32282,32283,[⟨[(235,1),(32280,1),(200692,((p:Int)-1))],[(32283,1)]⟩,⟨[(235,((p:Int)-1)),(32280,1),(200692,1)],[(32282,4),(32283,1)]⟩]⟩,⟨236,false,[(32282,1)],[(32284,1)],32284,32285,[⟨[(236,1),(32282,1),(200692,((p:Int)-1))],[(32285,1)]⟩,⟨[(236,((p:Int)-1)),(32282,1),(200692,1)],[(32284,4),(32285,1)]⟩]⟩,⟨237,false,[(32284,1)],[(32286,1)],32286,32287,[⟨[(237,1),(32284,1),(200692,((p:Int)-1))],[(32287,1)]⟩,⟨[(237,((p:Int)-1)),(32284,1),(200692,1)],[(32286,4),(32287,1)]⟩]⟩,⟨238,false,[(32286,1)],[(32288,1)],32288,32289,[⟨[(238,1),(32286,1),(200692,((p:Int)-1))],[(32289,1)]⟩,⟨[(238,((p:Int)-1)),(32286,1),(200692,1)],[(32288,4),(32289,1)]⟩]⟩,⟨239,false,[(32288,1)],[(32290,1)],32290,32291,[⟨[(239,1),(32288,1),(200692,((p:Int)-1))],[(32291,1)]⟩,⟨[(239,((p:Int)-1)),(32288,1),(200692,1)],[(32290,4),(32291,1)]⟩]⟩,⟨240,false,[(32290,1)],[(32292,1)],32292,32293,[⟨[(240,1),(32290,1),(200692,((p:Int)-1))],[(32293,1)]⟩,⟨[(240,((p:Int)-1)),(32290,1),(200692,1)],[(32292,4),(32293,1)]⟩]⟩,⟨241,false,[(32292,1)],[(32294,1)],32294,32295,[⟨[(241,1),(32292,1),(200692,((p:Int)-1))],[(32295,1)]⟩,⟨[(241,((p:Int)-1)),(32292,1),(200692,1)],[(32294,4),(32295,1)]⟩]⟩,⟨242,false,[(32294,1)],[(32296,1)],32296,32297,[⟨[(242,1),(32294,1),(200692,((p:Int)-1))],[(32297,1)]⟩,⟨[(242,((p:Int)-1)),(32294,1),(200692,1)],[(32296,4),(32297,1)]⟩]⟩,⟨243,false,[(32296,1)],[(32298,1)],32298,32299,[⟨[(243,1),(32296,1),(200692,((p:Int)-1))],[(32299,1)]⟩,⟨[(243,((p:Int)-1)),(32296,1),(200692,1)],[(32298,4),(32299,1)]⟩]⟩,⟨244,false,[(32298,1)],[(32300,1)],32300,32301,[⟨[(244,1),(32298,1),(200692,((p:Int)-1))],[(32301,1)]⟩,⟨[(244,((p:Int)-1)),(32298,1),(200692,1)],[(32300,4),(32301,1)]⟩]⟩,⟨245,false,[(32300,1)],[(32302,1)],32302,32303,[⟨[(245,1),(32300,1),(200692,((p:Int)-1))],[(32303,1)]⟩,⟨[(245,((p:Int)-1)),(32300,1),(200692,1)],[(32302,4),(32303,1)]⟩]⟩,⟨246,false,[(32302,1)],[(32304,1)],32304,32305,[⟨[(246,1),(32302,1),(200692,((p:Int)-1))],[(32305,1)]⟩,⟨[(246,((p:Int)-1)),(32302,1),(200692,1)],[(32304,4),(32305,1)]⟩]⟩,⟨247,false,[(32304,1)],[(32306,1)],32306,32307,[⟨[(247,1),(32304,1),(200692,((p:Int)-1))],[(32307,1)]⟩,⟨[(247,((p:Int)-1)),(32304,1),(200692,1)],[(32306,4),(32307,1)]⟩]⟩,⟨248,true,[(32306,1)],[(248,-1),(32308,1),(200692,1)],32308,32309,[⟨[(248,((p:Int)-1)),(32306,1)],[(32309,1)]⟩,⟨[(248,1),(32306,1)],[(32308,4),(32309,1)]⟩]⟩]
def initial : Linear := [(216,-1),(200692,1)]
def actualRows : List Row := entries.flatMap Entry.rows
noncomputable def productionCheck : Bool := chainCheck initial entries
theorem production_checked : productionCheck=true := by decide +kernel
noncomputable def rowCheck : Bool := CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 9508 64 actualRows
theorem rows_checked : rowCheck=true := by decide +kernel
theorem output_exact : output initial entries=[(248,-1),(32308,1),(200692,1)] := by rfl
variable {F : Type} [Field F] [CharP F p]
theorem semantic (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho (output initial entries)=rawScan rho (eval rho initial) entries :=
  chain_sound rho initial entries one production_checked
    (CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 9508 64
      actualRows rows_checked (by decide) rho arithmetic)
end ShielddSecurity.CapturedValueComparison102Pilot

set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison102Pilot.entries
#print axioms ShielddSecurity.CapturedValueComparison102Pilot.entries
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison102Pilot.initial
#print axioms ShielddSecurity.CapturedValueComparison102Pilot.initial
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison102Pilot.actualRows
#print axioms ShielddSecurity.CapturedValueComparison102Pilot.actualRows
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison102Pilot.productionCheck
#print axioms ShielddSecurity.CapturedValueComparison102Pilot.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison102Pilot.production_checked
#print axioms ShielddSecurity.CapturedValueComparison102Pilot.production_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison102Pilot.rowCheck
#print axioms ShielddSecurity.CapturedValueComparison102Pilot.rowCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison102Pilot.rows_checked
#print axioms ShielddSecurity.CapturedValueComparison102Pilot.rows_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison102Pilot.output_exact
#print axioms ShielddSecurity.CapturedValueComparison102Pilot.output_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison102Pilot.semantic
#print axioms ShielddSecurity.CapturedValueComparison102Pilot.semantic
