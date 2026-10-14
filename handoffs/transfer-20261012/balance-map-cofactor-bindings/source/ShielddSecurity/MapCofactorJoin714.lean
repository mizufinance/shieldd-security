import ShielddSecurity.MapCofactorCapture713
import ShielddSecurity.MapRational710
import ShielddSecurity.BalanceMapSeed703
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapCofactorJoin714
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01
open MapCofactorAdapter712
attribute [local irreducible] ConcreteCofactorModel01.model

structure Values (rho : Nat → F) (u : F) : Prop extends MapRational710.Values rho u where
  firstHint : rho 21195=BalanceMapSeed703.addInverse (BalanceMapPoint701.preimage u)
  secondHint : rho 21196=BalanceMapSeed703.addInverse (BalanceMapPoint701.twice u)
  thirdHint : rho 21197=BalanceMapSeed703.addInverse (BalanceMapPoint701.four u)

private theorem inverse_compat (p : Group.Point F) :
    BalanceMapSeed703.addInverse p=(CompilerSubgroupArithmetic79.inverseProduct coefficient p)⁻¹ := rfl

private theorem step (rho : Nat → F) (l : Layout) (p : Group.Point F)
    (one : rho copy=1) (equations : ∀ index<11, Equation rho l index)
    (coordinates : point rho l=p) (valid : Group.OnCurve coefficient p)
    (hint : rho l.hint=BalanceMapSeed703.addInverse p) :
    rho (l.start+6)=1 ∧ Group.Point.mk (rho (l.start+14)) (rho (l.start+18))=Group.affineAdd coefficient p p := by
  have hv : Group.OnCurve coefficient (point rho l) := coordinates.symm ▸ valid
  have hh : rho l.hint=(CompilerSubgroupArithmetic79.inverseProduct coefficient (point rho l))⁻¹ := by
    rw [coordinates]
    exact hint.trans (inverse_compat p)
  have result := complete rho l one equations hv hh
  rw [coordinates] at result
  exact result

private theorem twice_valid (u : F) : Group.OnCurve coefficient (BalanceMapPoint701.twice u) :=
  BalanceMapSeed703.addition_on_curve _ _ (BalanceMapPoint701.preimage_on_curve u) (BalanceMapPoint701.preimage_on_curve u)

private theorem four_valid (u : F) : Group.OnCurve coefficient (BalanceMapPoint701.four u) :=
  BalanceMapSeed703.addition_on_curve _ _ (twice_valid u) (twice_valid u)

private theorem first_step (rho : Nat → F) (u : F) (values : Values rho u)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 190189=1 ∧ Group.Point.mk (rho 190197) (rho 190201)=BalanceMapPoint701.twice u := by
  have initial := MapRational710.coordinates rho u values.toValues arithmetic
  have coordinates : point rho MapCofactorCapture713F00.layout=BalanceMapPoint701.preimage u := by
    simpa only [point,MapCofactorCapture713F00.layout,eval,Int.cast_one,one_mul,add_zero,MapRational710.point] using initial
  exact step rho MapCofactorCapture713F00.layout (BalanceMapPoint701.preimage u) values.copied
    (MapCofactorCapture713.equations rho arithmetic).1 coordinates (BalanceMapPoint701.preimage_on_curve u) values.firstHint

private theorem second_step (rho : Nat → F) (u : F) (values : Values rho u)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 190209=1 ∧ Group.Point.mk (rho 190217) (rho 190221)=BalanceMapPoint701.four u := by
  have coordinates : point rho MapCofactorCapture713F01.layout=BalanceMapPoint701.twice u := by
    simpa only [point,MapCofactorCapture713F01.layout,eval,Int.cast_one,one_mul,add_zero] using (first_step rho u values arithmetic).2
  exact step rho MapCofactorCapture713F01.layout (BalanceMapPoint701.twice u) values.copied
    (MapCofactorCapture713.equations rho arithmetic).2.1 coordinates (twice_valid u) values.secondHint

private theorem third_step (rho : Nat → F) (u : F) (values : Values rho u)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 190229=1 ∧ Group.Point.mk (rho 190237) (rho 190241)=BalanceMapPoint701.eight u := by
  have coordinates : point rho MapCofactorCapture713F02.layout=BalanceMapPoint701.four u := by
    simpa only [point,MapCofactorCapture713F02.layout,eval,Int.cast_one,one_mul,add_zero] using (second_step rho u values arithmetic).2
  exact step rho MapCofactorCapture713F02.layout (BalanceMapPoint701.four u) values.copied
    (MapCofactorCapture713.equations rho arithmetic).2.2 coordinates (four_valid u) values.thirdHint

theorem doublings (rho : Nat → F) (u : F) (values : Values rho u)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 190189=1 ∧ rho 190209=1 ∧ rho 190229=1 ∧
    Group.Point.mk (rho 190237) (rho 190241)=BalanceMapPoint701.eight u :=
  ⟨(first_step rho u values arithmetic).1,(second_step rho u values arithmetic).1,third_step rho u values arithmetic⟩

theorem base_coordinates (rho : Nat → F) (u : F) (values : Values rho u)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    Group.Point.mk (rho 190237) (rho 190241)=ConcreteCofactorModel01.model.coordinates (BalanceMapPoint701.represented u) :=
  (doublings rho u values arithmetic).2.2.2.trans (BalanceMapPoint701.represented_coordinates u).symm
end ShielddSecurity.MapCofactorJoin714

set_option pp.all true in
#check @ShielddSecurity.MapCofactorJoin714.Values.mk
#print axioms ShielddSecurity.MapCofactorJoin714.Values.mk

set_option pp.all true in
#check @ShielddSecurity.MapCofactorJoin714.doublings
#print axioms ShielddSecurity.MapCofactorJoin714.doublings

set_option pp.all true in
#check @ShielddSecurity.MapCofactorJoin714.base_coordinates
#print axioms ShielddSecurity.MapCofactorJoin714.base_coordinates
