"""Construct actual2/3base precomputations from the owned native input seed.

Finite support certificates preserve already constructed first-double rows.
Native address/issuer source-argument routing and the full126 loop are separate
joins; no incoming curve fact or desired circuit output is supplied here.
"""
from . import transfer_ownership_completion as completion
from . import generate_transfer_ownership_double_completion as double
from . import generate_transfer_ownership_add_completion as addition
from . import generate_transfer_ownership_native_seed as native
from .generate_hash_round import _signature_audits


def generate(checked, extracted, readonly_lcs=()):
    d, _ = double.generate(checked, extracted, readonly_lcs)
    a, _ = addition.generate(checked, extracted, readonly_lcs)
    n, _ = native.generate(checked, extracted, readonly_lcs)
    cones = completion.owner.cone_certificates(checked, extracted, 0, True)
    plan = completion.window_plan(checked, extracted, readonly_lcs=readonly_lcs)
    return render_precompute(checked,plan,cones,d,a,n)


def render_precompute(checked,plan,cones,d,a,n):
    """Neutral exact table precompute; source/native association stays explicit."""
    selected = {cone['role']: cone for cone in cones['cones']}
    observe = lambda identity: cones['observations'][identity][1]
    base = [observe(identity) for identity in selected['formula0']['inputs']]
    add_inputs = [observe(identity) for identity in selected['formula4']['inputs']]
    group = plan['point_groups'][0]
    quotient = plan['stages'][group['material_end']:group['stage_end']]
    expected = [((stage['quotient'], 1),) for stage in quotient] + base
    if add_inputs != expected:
        raise completion.relation.RelationError('ownership precompute exact2base/base coordinate source join')
    x, y = [terms[0][0] for terms in base]
    copy = checked['metadata']['constant_copy']
    c0 = d.removesuffix('Completion') + 'Cones'
    c1 = a.removesuffix('Completion') + 'Cones'
    m1 = a.removesuffix('Completion') + 'Materializations'
    name = d.removesuffix('Point0Completion') + 'NativePrecompute'
    source = f'''import ShielddSecurity.{n}
import ShielddSecurity.{a}
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
def writes : List Nat := {m1}.steps.flatMap GroupCircuitCompletion.Step.writes ++ {a}.x.writes ++ {a}.y.writes
def firstRows : List Row := {c0}.rawRows ++ {d}.quotientRaw
theorem addition_preserves {{F : Type}} [Field F] (base : Nat → F) (column : Nat)
    (outside : column ∉ writes) : {a}.completed base column = base column := by
  have materialOutside : ∀ step ∈ {m1}.steps, column ∉ step.writes := by
    intro step member present
    apply outside
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨step,member,present⟩))
  have outsideX : column ∉ {a}.x.writes := by
    intro present; exact outside (List.mem_append_left _ (List.mem_append_right _ present))
  have outsideY : column ∉ {a}.y.writes := by
    intro present; exact outside (List.mem_append_right _ present)
  exact (GroupQuotientPairCompletion.pair_preserves {a}.x {a}.y ({m1}.materialAssignment base)
    column outsideX outsideY).trans (GroupCircuitOrder.run_outside base {m1}.steps column materialOutside)
variable {{F : Type}} [Field F] [CharP F {d}.modulus]
variable {{E S R K Q Signing J : Type}} [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (model : Group.StandardCurveModel J ({c0}.coefficientD : F))
variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr ({c0}.coefficientD : F) model)
variable {{Encoded Native : Type}} (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
variable (point : S) (base : Nat → F)
def first : Nat → F := {n}.completed fq fr model upstream backend point base
def completed : Nat → F := {a}.completed (first fq fr model upstream backend point base)
theorem native_inputs (imaginary : F)
    (nonSquare : Group.NoUnitSquare ({c0}.coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
    (one : base 0 = 1) (linked : base {copy} = base 0) :
    {a}.inputPoint (first fq fr model upstream backend point base) = model.coordinates (2 • upstream.embed (upstream.promote point)) ∧
    {a}.rightPoint (first fq fr model upstream backend point base) = model.coordinates (upstream.embed (upstream.promote point)) := by
  let seed := {n}.seeded fq fr model upstream backend point base
  have seedLink : seed {copy} = seed 0 := by
    dsimp only [seed,{n}.seeded]
    rw [ShielddPointCoordinateSeed.seed_preserves fq fr ({c0}.coefficientD : F)
      model upstream backend point {x} {y} base {copy} (by decide),
      ShielddPointCoordinateSeed.seed_preserves fq fr ({c0}.coefficientD : F)
      model upstream backend point {x} {y} base 0 (by decide),linked]
  have doubled := ({n}.native_double_complete fq fr model upstream backend point base
    imaginary nonSquare imaginarySquare one linked).2
  have input := {n}.seeded_input fq fr model upstream backend point base
  constructor
  · have joined : {a}.inputPoint (first fq fr model upstream backend point base) =
        {d}.outputPoint (first fq fr model upstream backend point base) := by
      simp only [{a}.inputPoint,{a}.inputX,{a}.inputY,{d}.outputPoint,
        GroupQuotientPairCompletion.point,{d}.x,{d}.y,eval,Int.cast_one,one_mul,mul_one,add_zero]
    exact joined.trans doubled
  · change {a}.rightPoint ({d}.completed seed) = _
    have preserved := {d}.protected_columns seed seedLink
    have joined : {a}.rightPoint ({d}.completed seed) = {d}.inputPoint seed := by
      simp only [{a}.rightPoint,{a}.rightX,{a}.rightY,{d}.inputPoint,{d}.inputX,{d}.inputY,
        eval,Int.cast_one,one_mul,mul_one,add_zero]
      exact congrArg₂ Group.Point.mk (preserved {x} (by decide)) (preserved {y} (by decide))
    exact joined.trans input
theorem native_precompute_complete (imaginary : F)
    (nonSquare : Group.NoUnitSquare ({c0}.coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
    (one : base 0 = 1) (linked : base {copy} = base 0) :
    Satisfies (completed fq fr model upstream backend point base)
      (firstRows ++ {c1}.rawRows ++ {a}.quotientRaw) ∧
    {a}.outputPoint (completed fq fr model upstream backend point base) =
      model.coordinates (3 • upstream.embed (upstream.promote point)) := by
  let seed := {n}.seeded fq fr model upstream backend point base
  let built := first fq fr model upstream backend point base
  have seedOne : seed 0 = 1 :=
    (ShielddPointCoordinateSeed.seed_preserves fq fr ({c0}.coefficientD : F)
      model upstream backend point {x} {y} base 0 (by decide)).trans one
  have seedLink : seed {copy} = seed 0 := by
    dsimp only [seed,{n}.seeded]
    rw [ShielddPointCoordinateSeed.seed_preserves fq fr ({c0}.coefficientD : F)
      model upstream backend point {x} {y} base {copy} (by decide),
      ShielddPointCoordinateSeed.seed_preserves fq fr ({c0}.coefficientD : F)
      model upstream backend point {x} {y} base 0 (by decide),linked]
  have builtOne : built 0 = 1 := ({d}.protected_columns seed seedLink 0 (by decide)).trans seedOne
  have builtLink : built {copy} = built 0 := by
    change {d}.completed seed {copy} = {d}.completed seed 0
    rw [{d}.protected_columns seed seedLink {copy} (by decide),
      {d}.protected_columns seed seedLink 0 (by decide),seedLink]
  have inputs := native_inputs fq fr model upstream backend point base imaginary nonSquare imaginarySquare one linked
  have leftMeaning : {a}.inputPoint built = model.coordinates (2 • upstream.embed (upstream.promote point)) := inputs.1
  have rightMeaning : {a}.rightPoint built = model.coordinates (upstream.embed (upstream.promote point)) := inputs.2
  have leftValid : Group.OnCurve ({c1}.coefficientD : F) ({a}.inputPoint built) := by
    rw [leftMeaning]; exact model.onCurve _
  have rightValid : Group.OnCurve ({c1}.coefficientD : F) ({a}.rightPoint built) := by
    rw [rightMeaning]; exact model.onCurve _
  have addition := {a}.actual_point_complete imaginary nonSquare imaginarySquare built builtOne builtLink leftValid rightValid
  have earlier := ({n}.native_double_complete fq fr model upstream backend point base
    imaginary nonSquare imaginarySquare one linked).1
  have checked : firstRows.all (fun row => (row.a ++ row.b).all (fun term => decide (term.1 ∉ writes))) = true := by decide
  have retained : Satisfies ({a}.completed built) firstRows := by
    intro row member
    have agrees (terms : Linear) (inside : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
        eval ({a}.completed built) terms = eval built terms := by
      apply eval_agrees; intro term present
      exact addition_preserves built term.1 (of_decide_eq_true (List.all_eq_true.mp
        (List.all_eq_true.mp checked row member) term (inside term present)))
    change Square (eval ({a}.completed built) row.a) (eval ({a}.completed built) row.b)
    rw [agrees row.a (by intro term present; exact List.mem_append_left _ present),
      agrees row.b (by intro term present; exact List.mem_append_right _ present)]
    exact earlier row member
  constructor
  · intro row member
    rcases List.mem_append.mp member with first | last
    · rcases List.mem_append.mp first with before | middle
      · exact retained row before
      · exact addition.1 row (List.mem_append_left _ middle)
    · exact addition.1 row (List.mem_append_right _ last)
  · change {a}.outputPoint ({a}.completed built) = _
    rw [addition.2.1,leftMeaning,rightMeaning]
    have sameCoefficient : {c1}.coefficientD = {c0}.coefficientD := by decide
    rw [sameCoefficient,← model.addition]
    congr 1
    rw [show (3 : Nat) = 2 + 1 from rfl,add_nsmul,one_nsmul]
#print axioms addition_preserves
#print axioms native_inputs
#print axioms native_precompute_complete
end ShielddSecurity.{name}
'''
    return name, _signature_audits(source)
