-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.PointEqualityAdapter440
import ShielddSecurity.VariableWindowColumns449
import ShielddSecurity.AuthorizationFixedTables490
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedFamilyInitial555F02
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableWindowColumns449
def entry : PointEqualityAdapter440.Entry := ⟨[(8804,1)],[(8805,1)],[(8552,4139425550610461525665941076812662132363359224232624900223172373014329534291),(122076,1)],[(8552,39635691377166599497441725607757882405510648532010642268690928210480481875247),(122078,1),(200692,1)],8574,[⟨[(8552,48296449624515728953781799431373303705327193276295012922380486326924251650222),(8804,1),(122076,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩,⟨[(8552,12800183797959590982006014900428083432179903968516995553912730489458099309266),(8805,1),(122078,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩]⟩
theorem checked : PointEqualityAdapter440.check entry=true := by decide +kernel
def selector : FixedSelectorAdapter480.Entry := ⟨8552,8553,4139425550610461525665941076812662132363359224232624900223172373014329534291,39635691377166599497441725607757882405510648532010642268690928210480481875248,51649308687106732245355180334412183425352679808664353824402608302951341127598,42341045032719442200023627857290420958524899951475010660656175327133162357681,42747876515219196055051085994946250245437820367382162892902507989107803619675,47330627123043138289319845557100304432416973485572947695231610461184513390725,122076,122078,99338,[⟨[(8552,13040857722497997715970035416278595312278218665514815831723272686857867042214),(8553,1),(200692,786566488019458234092560173773782412337872691863283998201050396987240056915)],[(122077,1)]⟩,⟨[(8552,39395017452628192763477705091907370525412333835012821990880386013080714142299),(8553,1),(200692,51649308687106732245355180334412183425352679808664353824402608302951341127598)],[(122076,4),(122077,1)]⟩,⟨[(8552,34646109286842903408145507907947998931618574997912705234115493076429130842203),(8553,1),(200692,10094830142406748279424112650895544879165652549052627161947483372805418826833)],[(122079,1)]⟩,⟨[(8552,17789765888283287071302232600237966906071977502614932588488165623509450342310),(8553,1),(200692,42341045032719442200023627857290420958524899951475010660656175327133162357680)],[(122078,4),(122079,1)]⟩],[(8552,4139425550610461525665941076812662132363359224232624900223172373014329534291),(122076,1)],[(8552,39635691377166599497441725607757882405510648532010642268690928210480481875247),(122078,1),(200692,1)]⟩
theorem selector_checked : FixedSelectorAdapter480.check selector=true := by decide +kernel
theorem rows_iff {F : Type} [Field F] [CharP F p] (rho : Nat → F)
    (one : rho copy=1) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8574+i)) 2 ↔
      columnPoint rho 8804=Group.windowPoint (rho 8552) (rho 8553)
        (FixedSelectorAdapter480.base selector) (FixedSelectorAdapter480.twice selector)
        (FixedSelectorAdapter480.triple selector) := by
  have equivalence := PointEqualityAdapter440.equality_iff entry checked rho
  have x : canonical p entry.expectedX=canonical p selector.outputX := by decide +kernel
  have y : canonical p entry.expectedY=canonical p selector.outputY := by decide +kernel
  rw [canonical_equal rho _ _ x,canonical_equal rho _ _ y] at equivalence
  have outputX : entry.outputX=[(8804,1)] := rfl
  have outputY : entry.outputY=[(8805,1)] := rfl
  rw [outputX,outputY] at equivalence
  simp only [eval,Int.cast_one,one_mul,add_zero] at equivalence
  rw [FixedSelectorAdapter480.coordinates selector selector_checked rho one arithmetic] at equivalence
  exact equivalence

theorem table_points :
    (FixedSelectorAdapter480.base selector : Group.Point ConcreteJubjubField01.F)=FixedSelectorAdapter480.base (AuthorizationFixedTables490.table 0).1 ∧
    (FixedSelectorAdapter480.twice selector : Group.Point ConcreteJubjubField01.F)=FixedSelectorAdapter480.twice (AuthorizationFixedTables490.table 0).1 ∧
    (FixedSelectorAdapter480.triple selector : Group.Point ConcreteJubjubField01.F)=FixedSelectorAdapter480.triple (AuthorizationFixedTables490.table 0).1 := by
  exact ⟨rfl,rfl,rfl⟩

end ShielddSecurity.FixedFamilyInitial555F02
set_option pp.all true in
#check @ShielddSecurity.FixedFamilyInitial555F02.checked
#print axioms ShielddSecurity.FixedFamilyInitial555F02.checked
set_option pp.all true in
#check @ShielddSecurity.FixedFamilyInitial555F02.selector_checked
#print axioms ShielddSecurity.FixedFamilyInitial555F02.selector_checked
set_option pp.all true in
#check @ShielddSecurity.FixedFamilyInitial555F02.rows_iff
#print axioms ShielddSecurity.FixedFamilyInitial555F02.rows_iff
set_option pp.all true in
#check @ShielddSecurity.FixedFamilyInitial555F02.table_points
#print axioms ShielddSecurity.FixedFamilyInitial555F02.table_points
