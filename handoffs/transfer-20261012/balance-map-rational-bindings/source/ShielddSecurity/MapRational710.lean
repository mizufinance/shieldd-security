import ShielddSecurity.MapSelected709
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapRational710
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01
open BalanceMapParameters699 MapSelected709

-- These are explicit witness-value premises, not assumptions of satisfied map rows.
structure Values (rho : Nat → F) (u : F) : Prop where
  copied : rho copy=1
  initialInverse : rho 20934=(sourceDenominator u)⁻¹
  flag : rho 20935=if BalanceMapRoots700.choice u then 1 else 0
  selected : rho 20937=BalanceMapRoots700.selectedRoot u
  zero : rho 21193=BalanceMapPoint701.zero u
  inverse : rho 21194=(BalanceMapPoint701.denominator u)⁻¹

theorem denominator_value (rho : Nat → F) (u : F) (values : Values rho u)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 190167=BalanceMapPoint701.denominator u := by
  have s := s_value rho u values.copied values.initialInverse values.flag arithmetic
  exact mul_output MapArithmeticCapture705B01.entry1 190167 MapArithmeticCapture705B01.checked1 rfl rfl rho arithmetic _ _
    (plus_value rho u values.copied s) (t_value rho u values.selected)

theorem inverse_values (rho : Nat → F) (u : F) (values : Values rho u)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 190169=1-BalanceMapPoint701.zero u ∧ rho 190171=0 ∧ rho 190173=0 := by
  have denom := denominator_value rho u values arithmetic
  have first := mul_output MapArithmeticCapture705B01.entry2 190169 MapArithmeticCapture705B01.checked2 rfl rfl rho arithmetic _ _
    (by simpa only [MapArithmeticCapture705B01.entry2,eval,Int.cast_one,one_mul,add_zero] using denom)
    (by simpa only [MapArithmeticCapture705B01.entry2,eval,Int.cast_one,one_mul,add_zero] using values.inverse)
  have second := mul_output MapArithmeticCapture705B01.entry3 190171 MapArithmeticCapture705B01.checked3 rfl rfl rho arithmetic _ _
    (by simpa only [MapArithmeticCapture705B01.entry3,eval,Int.cast_one,one_mul,add_zero] using denom)
    (by simpa only [MapArithmeticCapture705B01.entry3,eval,Int.cast_one,one_mul,add_zero] using values.zero)
  have third := mul_output MapArithmeticCapture705B01.entry4 190173 MapArithmeticCapture705B01.checked4 rfl rfl rho arithmetic _ _
    (by simpa only [MapArithmeticCapture705B01.entry4,eval,Int.cast_one,one_mul,add_zero] using values.inverse)
    (by simpa only [MapArithmeticCapture705B01.entry4,eval,Int.cast_one,one_mul,add_zero] using values.zero)
  have equations := BalanceMapPoint701.inverse_constraints u
  exact ⟨first.trans equations.1,second.trans equations.2.1,third.trans equations.2.2⟩

def point (rho : Nat → F) : Group.Point F := ⟨rho 190177,rho 21193+rho 190181⟩

theorem coordinates (rho : Nat → F) (u : F) (values : Values rho u)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : point rho=BalanceMapPoint701.preimage u := by
  have s := s_value rho u values.copied values.initialInverse values.flag arithmetic
  have plus := plus_value rho u values.copied s
  have minus := minus_value rho u values.copied s
  have t := t_value rho u values.selected
  have auxX := mul_output MapArithmeticCapture705B01.entry5 190175 MapArithmeticCapture705B01.checked5 rfl rfl rho arithmetic _ _
    (by simpa only [MapArithmeticCapture705B01.entry5,eval,Int.cast_one,one_mul,add_zero] using values.inverse) plus
  have x := mul_output MapArithmeticCapture705B01.entry6 190177 MapArithmeticCapture705B01.checked6 rfl rfl rho arithmetic _ _
    (by simpa only [MapArithmeticCapture705B01.entry6,eval,Int.cast_one,one_mul,add_zero] using auxX) s
  have auxY := mul_output MapArithmeticCapture705B02.entry0 190179 MapArithmeticCapture705B02.checked0 rfl rfl rho arithmetic _ _
    (by simpa only [MapArithmeticCapture705B02.entry0,eval,Int.cast_one,one_mul,add_zero] using values.inverse) t
  have y := mul_output MapArithmeticCapture705B02.entry1 190181 MapArithmeticCapture705B02.checked1 rfl rfl rho arithmetic _ _
    (by simpa only [MapArithmeticCapture705B02.entry1,eval,Int.cast_one,one_mul,add_zero] using auxY) minus
  change Group.Point.mk (rho 190177) (rho 21193+rho 190181)=
    Group.Point.mk ((BalanceMapPoint701.denominator u)⁻¹*(BalanceMapPoint701.s u+1)*BalanceMapPoint701.s u)
      ((BalanceMapPoint701.denominator u)⁻¹*BalanceMapPoint701.t u*(BalanceMapPoint701.s u-1)+BalanceMapPoint701.zero u)
  apply congrArg₂ Group.Point.mk
  · exact x
  · rw [values.zero,y]
    ring

theorem on_curve (rho : Nat → F) (u : F) (values : Values rho u)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : Group.OnCurve coefficient (point rho) := by
  rw [coordinates rho u values arithmetic]
  exact BalanceMapPoint701.preimage_on_curve u
end ShielddSecurity.MapRational710

set_option pp.all true in
#check @ShielddSecurity.MapRational710.Values.mk
#print axioms ShielddSecurity.MapRational710.Values.mk

set_option pp.all true in
#check @ShielddSecurity.MapRational710.denominator_value
#print axioms ShielddSecurity.MapRational710.denominator_value

set_option pp.all true in
#check @ShielddSecurity.MapRational710.inverse_values
#print axioms ShielddSecurity.MapRational710.inverse_values

set_option pp.all true in
#check @ShielddSecurity.MapRational710.coordinates
#print axioms ShielddSecurity.MapRational710.coordinates

set_option pp.all true in
#check @ShielddSecurity.MapRational710.on_curve
#print axioms ShielddSecurity.MapRational710.on_curve
