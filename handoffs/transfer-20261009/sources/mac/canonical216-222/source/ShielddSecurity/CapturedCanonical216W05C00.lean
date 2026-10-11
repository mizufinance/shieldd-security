import ShielddSecurity.CanonicalComparisonSlices218
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedCanonical216W05C00
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ComparisonCertificate101
def entries : List Entry := [⟨727,false,[(726,-1),(200692,1)],[(33262,1)],33262,33263,[⟨[(726,((p:Int)-1)),(727,1)],[(33263,1)]⟩,⟨[(726,((p:Int)-1)),(727,((p:Int)-1)),(200692,2)],[(33262,4),(33263,1)]⟩]⟩,⟨728,false,[(33262,1)],[(33264,1)],33264,33265,[⟨[(728,1),(33262,1),(200692,((p:Int)-1))],[(33265,1)]⟩,⟨[(728,((p:Int)-1)),(33262,1),(200692,1)],[(33264,4),(33265,1)]⟩]⟩,⟨729,false,[(33264,1)],[(33266,1)],33266,33267,[⟨[(729,1),(33264,1),(200692,((p:Int)-1))],[(33267,1)]⟩,⟨[(729,((p:Int)-1)),(33264,1),(200692,1)],[(33266,4),(33267,1)]⟩]⟩,⟨730,false,[(33266,1)],[(33268,1)],33268,33269,[⟨[(730,1),(33266,1),(200692,((p:Int)-1))],[(33269,1)]⟩,⟨[(730,((p:Int)-1)),(33266,1),(200692,1)],[(33268,4),(33269,1)]⟩]⟩,⟨731,false,[(33268,1)],[(33270,1)],33270,33271,[⟨[(731,1),(33268,1),(200692,((p:Int)-1))],[(33271,1)]⟩,⟨[(731,((p:Int)-1)),(33268,1),(200692,1)],[(33270,4),(33271,1)]⟩]⟩,⟨732,false,[(33270,1)],[(33272,1)],33272,33273,[⟨[(732,1),(33270,1),(200692,((p:Int)-1))],[(33273,1)]⟩,⟨[(732,((p:Int)-1)),(33270,1),(200692,1)],[(33272,4),(33273,1)]⟩]⟩,⟨733,false,[(33272,1)],[(33274,1)],33274,33275,[⟨[(733,1),(33272,1),(200692,((p:Int)-1))],[(33275,1)]⟩,⟨[(733,((p:Int)-1)),(33272,1),(200692,1)],[(33274,4),(33275,1)]⟩]⟩,⟨734,false,[(33274,1)],[(33276,1)],33276,33277,[⟨[(734,1),(33274,1),(200692,((p:Int)-1))],[(33277,1)]⟩,⟨[(734,((p:Int)-1)),(33274,1),(200692,1)],[(33276,4),(33277,1)]⟩]⟩,⟨735,false,[(33276,1)],[(33278,1)],33278,33279,[⟨[(735,1),(33276,1),(200692,((p:Int)-1))],[(33279,1)]⟩,⟨[(735,((p:Int)-1)),(33276,1),(200692,1)],[(33278,4),(33279,1)]⟩]⟩,⟨736,false,[(33278,1)],[(33280,1)],33280,33281,[⟨[(736,1),(33278,1),(200692,((p:Int)-1))],[(33281,1)]⟩,⟨[(736,((p:Int)-1)),(33278,1),(200692,1)],[(33280,4),(33281,1)]⟩]⟩,⟨737,false,[(33280,1)],[(33282,1)],33282,33283,[⟨[(737,1),(33280,1),(200692,((p:Int)-1))],[(33283,1)]⟩,⟨[(737,((p:Int)-1)),(33280,1),(200692,1)],[(33282,4),(33283,1)]⟩]⟩,⟨738,false,[(33282,1)],[(33284,1)],33284,33285,[⟨[(738,1),(33282,1),(200692,((p:Int)-1))],[(33285,1)]⟩,⟨[(738,((p:Int)-1)),(33282,1),(200692,1)],[(33284,4),(33285,1)]⟩]⟩,⟨739,false,[(33284,1)],[(33286,1)],33286,33287,[⟨[(739,1),(33284,1),(200692,((p:Int)-1))],[(33287,1)]⟩,⟨[(739,((p:Int)-1)),(33284,1),(200692,1)],[(33286,4),(33287,1)]⟩]⟩,⟨740,false,[(33286,1)],[(33288,1)],33288,33289,[⟨[(740,1),(33286,1),(200692,((p:Int)-1))],[(33289,1)]⟩,⟨[(740,((p:Int)-1)),(33286,1),(200692,1)],[(33288,4),(33289,1)]⟩]⟩,⟨741,false,[(33288,1)],[(33290,1)],33290,33291,[⟨[(741,1),(33288,1),(200692,((p:Int)-1))],[(33291,1)]⟩,⟨[(741,((p:Int)-1)),(33288,1),(200692,1)],[(33290,4),(33291,1)]⟩]⟩,⟨742,false,[(33290,1)],[(33292,1)],33292,33293,[⟨[(742,1),(33290,1),(200692,((p:Int)-1))],[(33293,1)]⟩,⟨[(742,((p:Int)-1)),(33290,1),(200692,1)],[(33292,4),(33293,1)]⟩]⟩,⟨743,false,[(33292,1)],[(33294,1)],33294,33295,[⟨[(743,1),(33292,1),(200692,((p:Int)-1))],[(33295,1)]⟩,⟨[(743,((p:Int)-1)),(33292,1),(200692,1)],[(33294,4),(33295,1)]⟩]⟩,⟨744,false,[(33294,1)],[(33296,1)],33296,33297,[⟨[(744,1),(33294,1),(200692,((p:Int)-1))],[(33297,1)]⟩,⟨[(744,((p:Int)-1)),(33294,1),(200692,1)],[(33296,4),(33297,1)]⟩]⟩,⟨745,false,[(33296,1)],[(33298,1)],33298,33299,[⟨[(745,1),(33296,1),(200692,((p:Int)-1))],[(33299,1)]⟩,⟨[(745,((p:Int)-1)),(33296,1),(200692,1)],[(33298,4),(33299,1)]⟩]⟩,⟨746,false,[(33298,1)],[(33300,1)],33300,33301,[⟨[(746,1),(33298,1),(200692,((p:Int)-1))],[(33301,1)]⟩,⟨[(746,((p:Int)-1)),(33298,1),(200692,1)],[(33300,4),(33301,1)]⟩]⟩,⟨747,false,[(33300,1)],[(33302,1)],33302,33303,[⟨[(747,1),(33300,1),(200692,((p:Int)-1))],[(33303,1)]⟩,⟨[(747,((p:Int)-1)),(33300,1),(200692,1)],[(33302,4),(33303,1)]⟩]⟩,⟨748,false,[(33302,1)],[(33304,1)],33304,33305,[⟨[(748,1),(33302,1),(200692,((p:Int)-1))],[(33305,1)]⟩,⟨[(748,((p:Int)-1)),(33302,1),(200692,1)],[(33304,4),(33305,1)]⟩]⟩,⟨749,false,[(33304,1)],[(33306,1)],33306,33307,[⟨[(749,1),(33304,1),(200692,((p:Int)-1))],[(33307,1)]⟩,⟨[(749,((p:Int)-1)),(33304,1),(200692,1)],[(33306,4),(33307,1)]⟩]⟩,⟨750,false,[(33306,1)],[(33308,1)],33308,33309,[⟨[(750,1),(33306,1),(200692,((p:Int)-1))],[(33309,1)]⟩,⟨[(750,((p:Int)-1)),(33306,1),(200692,1)],[(33308,4),(33309,1)]⟩]⟩,⟨751,false,[(33308,1)],[(33310,1)],33310,33311,[⟨[(751,1),(33308,1),(200692,((p:Int)-1))],[(33311,1)]⟩,⟨[(751,((p:Int)-1)),(33308,1),(200692,1)],[(33310,4),(33311,1)]⟩]⟩,⟨752,false,[(33310,1)],[(33312,1)],33312,33313,[⟨[(752,1),(33310,1),(200692,((p:Int)-1))],[(33313,1)]⟩,⟨[(752,((p:Int)-1)),(33310,1),(200692,1)],[(33312,4),(33313,1)]⟩]⟩,⟨753,false,[(33312,1)],[(33314,1)],33314,33315,[⟨[(753,1),(33312,1),(200692,((p:Int)-1))],[(33315,1)]⟩,⟨[(753,((p:Int)-1)),(33312,1),(200692,1)],[(33314,4),(33315,1)]⟩]⟩,⟨754,false,[(33314,1)],[(33316,1)],33316,33317,[⟨[(754,1),(33314,1),(200692,((p:Int)-1))],[(33317,1)]⟩,⟨[(754,((p:Int)-1)),(33314,1),(200692,1)],[(33316,4),(33317,1)]⟩]⟩,⟨755,false,[(33316,1)],[(33318,1)],33318,33319,[⟨[(755,1),(33316,1),(200692,((p:Int)-1))],[(33319,1)]⟩,⟨[(755,((p:Int)-1)),(33316,1),(200692,1)],[(33318,4),(33319,1)]⟩]⟩,⟨756,false,[(33318,1)],[(33320,1)],33320,33321,[⟨[(756,1),(33318,1),(200692,((p:Int)-1))],[(33321,1)]⟩,⟨[(756,((p:Int)-1)),(33318,1),(200692,1)],[(33320,4),(33321,1)]⟩]⟩,⟨757,false,[(33320,1)],[(33322,1)],33322,33323,[⟨[(757,1),(33320,1),(200692,((p:Int)-1))],[(33323,1)]⟩,⟨[(757,((p:Int)-1)),(33320,1),(200692,1)],[(33322,4),(33323,1)]⟩]⟩,⟨758,true,[(33322,1)],[(758,-1),(33324,1),(200692,1)],33324,33325,[⟨[(758,((p:Int)-1)),(33322,1)],[(33325,1)]⟩,⟨[(758,1),(33322,1)],[(33324,4),(33325,1)]⟩]⟩]
def initial : Linear := [(726,-1),(200692,1)]
def actualRows : List Row := entries.flatMap Entry.rows
noncomputable def productionCheck : Bool := chainCheck initial entries
theorem production_checked : productionCheck=true := by decide +kernel
noncomputable def rowCheck : Bool := CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 10524 64 actualRows
theorem rows_checked : rowCheck=true := by decide +kernel
theorem output_exact : output initial entries=[(758,-1),(33324,1),(200692,1)] := by rfl
theorem selected : ∀ row∈entries.flatMap Entry.rows,∃ index<177954,CapturedFullArithmetic52.rowAt index=some row :=
 CanonicalComparisonSlices218.slice 10524 64 actualRows rows_checked (by decide)
end ShielddSecurity.CapturedCanonical216W05C00

set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W05C00.entries
#print axioms ShielddSecurity.CapturedCanonical216W05C00.entries
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W05C00.initial
#print axioms ShielddSecurity.CapturedCanonical216W05C00.initial
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W05C00.actualRows
#print axioms ShielddSecurity.CapturedCanonical216W05C00.actualRows
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W05C00.productionCheck
#print axioms ShielddSecurity.CapturedCanonical216W05C00.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W05C00.production_checked
#print axioms ShielddSecurity.CapturedCanonical216W05C00.production_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W05C00.rowCheck
#print axioms ShielddSecurity.CapturedCanonical216W05C00.rowCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W05C00.rows_checked
#print axioms ShielddSecurity.CapturedCanonical216W05C00.rows_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W05C00.output_exact
#print axioms ShielddSecurity.CapturedCanonical216W05C00.output_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedCanonical216W05C00.selected
#print axioms ShielddSecurity.CapturedCanonical216W05C00.selected
