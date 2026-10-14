-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.PointEqualityAdapter440
import ShielddSecurity.VariableWindowColumns449
import ShielddSecurity.BalanceBlindingTables673
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingInitial684F00
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableWindowColumns449
noncomputable def entry : PointEqualityAdapter440.Entry := ⟨[(22484,1)],[(22485,1)],[(22232,47042227020334719030310671629496501061777616454137182971856918820250544653111),(193210,1)],[(22232,49531484613049745751551498609154147537293487462303198979615882148044956461706),(193212,1),(200692,1)],22559,[⟨[(22232,5393648154791471449137068878689464775912936046390454850746739879688036531402),(22484,1),(193210,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩,⟨[(22232,2904390562076444727896241899031818300397065038224438842987776551893624722807),(22485,1),(193212,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩]⟩
theorem checked : PointEqualityAdapter440.check entry=true := by decide +kernel
noncomputable def selector : FixedSelectorAdapter480.Entry := ⟨22232,22233,47042227020334719030310671629496501061777616454137182971856918820250544653111,49531484613049745751551498609154147537293487462303198979615882148044956461707,40080219597527953451895930579352708423782856735052156902032814884658164133529,32249997739105904846998615368250744883722066700221205992682927936656794178531,1595057811895567985432350693947327218736082967595313618207906895344514089150,7252898302633483926745090484325162191312609498704787453545142920044319718216,193210,193212,170472,[⟨[(22232,33091513630840914017326511006715916429133837721066388433078168109625613512977),(22233,1),(200692,12355655577598237027551809928833257413907695765475480920570843815280417050984)],[(193211,1)]⟩,⟨[(22232,19344361544285276462121229501470049408556714779461249389525490590312967671536),(22233,1),(200692,40080219597527953451895930579352708423782856735052156902032814884658164133529)],[(193210,4),(193211,1)]⟩,⟨[(22232,22092708874395976192357282984893764392012392163291979696150008464718849737508),(22233,1),(200692,20185877436020285632449125139935220953968485800306431829920730763281787005983)],[(193213,1)]⟩,⟨[(22232,30343166300730214287090457523292201445678160337235658126453650235219731447005),(22233,1),(200692,32249997739105904846998615368250744883722066700221205992682927936656794178530)],[(193212,4),(193213,1)]⟩],[(22232,47042227020334719030310671629496501061777616454137182971856918820250544653111),(193210,1)],[(22232,49531484613049745751551498609154147537293487462303198979615882148044956461706),(193212,1),(200692,1)]⟩
theorem selector_checked : FixedSelectorAdapter480.check selector=true := by decide +kernel
theorem rows_iff {F : Type} [Field F] [CharP F p] (rho : Nat → F)
    (one : rho copy=1) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+22559+i)) 2 ↔
      columnPoint rho 22484=Group.windowPoint (rho 22232) (rho 22233)
        (FixedSelectorAdapter480.base selector) (FixedSelectorAdapter480.twice selector)
        (FixedSelectorAdapter480.triple selector) := by
  have equivalence := PointEqualityAdapter440.equality_iff entry checked rho
  have x : canonical p entry.expectedX=canonical p selector.outputX := by decide +kernel
  have y : canonical p entry.expectedY=canonical p selector.outputY := by decide +kernel
  rw [canonical_equal rho _ _ x,canonical_equal rho _ _ y] at equivalence
  have outputX : entry.outputX=[(22484,1)] := rfl
  have outputY : entry.outputY=[(22485,1)] := rfl
  rw [outputX,outputY] at equivalence
  simp only [eval,Int.cast_one,one_mul,add_zero] at equivalence
  rw [FixedSelectorAdapter480.coordinates selector selector_checked rho one arithmetic] at equivalence
  exact equivalence

theorem table_points :
    (FixedSelectorAdapter480.base selector : Group.Point ConcreteJubjubField01.F)=FixedSelectorAdapter480.base (BalanceBlindingTables673.table 0).1 ∧
    (FixedSelectorAdapter480.twice selector : Group.Point ConcreteJubjubField01.F)=FixedSelectorAdapter480.twice (BalanceBlindingTables673.table 0).1 ∧
    (FixedSelectorAdapter480.triple selector : Group.Point ConcreteJubjubField01.F)=FixedSelectorAdapter480.triple (BalanceBlindingTables673.table 0).1 := by
  exact ⟨rfl,rfl,rfl⟩

end ShielddSecurity.BalanceBlindingInitial684F00
set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingInitial684F00.checked
#print axioms ShielddSecurity.BalanceBlindingInitial684F00.checked
set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingInitial684F00.selector_checked
#print axioms ShielddSecurity.BalanceBlindingInitial684F00.selector_checked
set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingInitial684F00.rows_iff
#print axioms ShielddSecurity.BalanceBlindingInitial684F00.rows_iff
set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingInitial684F00.table_points
#print axioms ShielddSecurity.BalanceBlindingInitial684F00.table_points
