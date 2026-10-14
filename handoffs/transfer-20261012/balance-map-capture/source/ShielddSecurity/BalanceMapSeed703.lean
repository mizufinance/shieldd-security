import ShielddSecurity.BalanceMapPoint701
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceMapSeed703
open ConcreteJubjubField01 BalanceMapParameters699
attribute [local irreducible] ConcreteCofactorModel01.model

def addDenominator (point : Group.Point F) : F :=
  (1+Group.delta coefficient point point)*(1-Group.delta coefficient point point)
def addInverse (point : Group.Point F) : F := (addDenominator point)⁻¹

theorem addition_on_curve (left right : Group.Point F)
    (hl : Group.OnCurve coefficient left) (hr : Group.OnCurve coefficient right) :
    Group.OnCurve coefficient (Group.affineAdd coefficient left right) := by
  obtain ⟨p,hp⟩ := ConcreteCofactorModel01.model.covers left hl
  obtain ⟨q,hq⟩ := ConcreteCofactorModel01.model.covers right hr
  rw [← hp,← hq,← ConcreteCofactorModel01.model.addition]
  exact ConcreteCofactorModel01.model.onCurve (p+q)

theorem inverse_equation (point : Group.Point F) (valid : Group.OnCurve coefficient point) :
    addInverse point*addDenominator point=1 := by
  have factors := Group.denominators_nonzero coefficient imaginary coefficient_no_unit_square imaginary_square point point valid valid
  exact inv_mul_cancel₀ (mul_ne_zero factors.1 factors.2)

theorem three_inverses (u : F) :
    addInverse (BalanceMapPoint701.preimage u)*addDenominator (BalanceMapPoint701.preimage u)=1 ∧
    addInverse (BalanceMapPoint701.twice u)*addDenominator (BalanceMapPoint701.twice u)=1 ∧
    addInverse (BalanceMapPoint701.four u)*addDenominator (BalanceMapPoint701.four u)=1 := by
  have first := BalanceMapPoint701.preimage_on_curve u
  have second := addition_on_curve _ _ first first
  have third := addition_on_curve _ _ second second
  exact ⟨inverse_equation _ first,inverse_equation _ second,inverse_equation _ third⟩

-- Exact witness columns are recorded from the pinned capture. Their preservation
-- through the cumulative assignment and captured arithmetic remains separate.
def columns : List Nat := [20934,20935,20936,20937,21193,21194,21195,21196,21197,21198]
noncomputable def value (u : F) (column : Nat) : F :=
  if column=20934 then (sourceDenominator u)⁻¹
  else if column=20935 then (if BalanceMapRoots700.choice u then 1 else 0)
  else if column=20936 then BalanceMapRoots700.qrRoot u
  else if column=20937 then BalanceMapRoots700.selectedRoot u
  else if column=21193 then BalanceMapPoint701.zero u
  else if column=21194 then (BalanceMapPoint701.denominator u)⁻¹
  else if column=21195 then addInverse (BalanceMapPoint701.preimage u)
  else if column=21196 then addInverse (BalanceMapPoint701.twice u)
  else if column=21197 then addInverse (BalanceMapPoint701.four u)
  else if column=21198 then (BalanceMapPoint701.eight u).x⁻¹
  else 0
noncomputable def seed (original : Nat → F) (u : F) (column : Nat) : F :=
  if column∈columns then value u column else original column

theorem seed_value (original : Nat → F) (u : F) (column : Nat) (member : column∈columns) :
    seed original u column=value u column := if_pos member

theorem outside (original : Nat → F) (u : F) (column : Nat) (absent : column∉columns) :
    seed original u column=original column := if_neg absent

theorem initial_inverse (u : F) : value u 20934*sourceDenominator u=1 := by
  change (sourceDenominator u)⁻¹*sourceDenominator u=1
  exact inv_mul_cancel₀ (actual_elligator_denominator_is_nonzero u)

theorem nonidentity_inverse (u : F) (nonzero : (BalanceMapPoint701.eight u).x≠0) :
    value u 21198*(BalanceMapPoint701.eight u).x=1 := by
  change (BalanceMapPoint701.eight u).x⁻¹*(BalanceMapPoint701.eight u).x=1
  exact inv_mul_cancel₀ nonzero
end ShielddSecurity.BalanceMapSeed703

set_option pp.all true in
#check @ShielddSecurity.BalanceMapSeed703.addition_on_curve
#print axioms ShielddSecurity.BalanceMapSeed703.addition_on_curve

set_option pp.all true in
#check @ShielddSecurity.BalanceMapSeed703.inverse_equation
#print axioms ShielddSecurity.BalanceMapSeed703.inverse_equation

set_option pp.all true in
#check @ShielddSecurity.BalanceMapSeed703.three_inverses
#print axioms ShielddSecurity.BalanceMapSeed703.three_inverses

set_option pp.all true in
#check @ShielddSecurity.BalanceMapSeed703.seed_value
#print axioms ShielddSecurity.BalanceMapSeed703.seed_value

set_option pp.all true in
#check @ShielddSecurity.BalanceMapSeed703.outside
#print axioms ShielddSecurity.BalanceMapSeed703.outside

set_option pp.all true in
#check @ShielddSecurity.BalanceMapSeed703.initial_inverse
#print axioms ShielddSecurity.BalanceMapSeed703.initial_inverse

set_option pp.all true in
#check @ShielddSecurity.BalanceMapSeed703.nonidentity_inverse
#print axioms ShielddSecurity.BalanceMapSeed703.nonidentity_inverse
