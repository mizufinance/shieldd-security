"""Actual precompute write footprint and arbitrary-column preservation.

This is a preservation boundary, not a prefix constructor. Bounded original
row support certificates can feed it after the native IVK constructor proves
those rows. The footprint includes the source coordinate seed explicitly.
"""
from . import generate_transfer_ownership_precompute_tables as tables
from .generate_hash_round import _signature_audits


def generate(checked, extracted, readonly_lcs=()):
    table_name, _ = tables.generate(checked, extracted, readonly_lcs)
    stem = table_name.removesuffix('NativeTables')
    n = stem+'NativePrecompute'; d = stem+'Point0Completion'
    m = stem+'Point0Materializations'; seed = d+'NativeSeed'
    cones = tables.completion.owner.cone_certificates(checked, extracted, 0, True)
    formula = next(cone for cone in cones['cones'] if cone['role']=='formula0')
    inputs = [cones['observations'][identity][1] for identity in formula['inputs']]
    # tables.generate has already checked the actual singleton/source/table join.
    x, y = [terms[0][0] for terms in inputs]
    name = stem+'PrecomputeFrame'
    source = f'''import ShielddSecurity.{n}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
def writes : List Nat := [{x},{y}] ++ ({m}.steps.flatMap GroupCircuitCompletion.Step.writes
  ++ ({d}.x.writes ++ ({d}.y.writes ++ {n}.writes)))
variable {{F : Type}} [Field F] [CharP F {d}.modulus]
variable {{E S R K Q Signing J : Type}} [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (model : Group.StandardCurveModel J ({stem}Point0Cones.coefficientD : F))
variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr ({stem}Point0Cones.coefficientD : F) model)
variable {{Encoded Native : Type}} (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
variable (point : S) (base : Nat → F)
theorem outside (column : Nat) (notWritten : column ∉ writes) :
    {n}.completed fq fr model upstream backend point base column = base column := by
  have excluded : column ∉ [{x},{y}] ∧
      column ∉ {m}.steps.flatMap GroupCircuitCompletion.Step.writes ∧
      column ∉ {d}.x.writes ∧ column ∉ {d}.y.writes ∧ column ∉ {n}.writes := by
    simpa only [writes,List.mem_append,not_or] using notWritten
  have materialOutside : ∀ step ∈ {m}.steps, column ∉ step.writes := by
    intro step member written
    exact excluded.2.1 (List.mem_flatMap.mpr ⟨step,member,written⟩)
  let seeded := {seed}.seeded fq fr model upstream backend point base
  have firstKeep : {n}.first fq fr model upstream backend point base column = seeded column := by
    change GroupQuotientPairCompletion.build {d}.x {d}.y
      ({m}.materialAssignment seeded) column = seeded column
    exact (GroupQuotientPairCompletion.pair_preserves {d}.x {d}.y
      ({m}.materialAssignment seeded) column excluded.2.2.1 excluded.2.2.2.1).trans
      (GroupCircuitOrder.run_outside seeded {m}.steps column materialOutside)
  exact ({n}.addition_preserves ({n}.first fq fr model upstream backend point base)
    column excluded.2.2.2.2).trans (firstKeep.trans
      (ShielddPointCoordinateSeed.seed_preserves fq fr ({stem}Point0Cones.coefficientD : F)
        model upstream backend point {x} {y} base column excluded.1))

theorem rows_preserved (rows : List Row) (earlier : Satisfies base rows)
    (support : ∀ row ∈ rows, ∀ term ∈ row.a ++ row.b, term.1 ∉ writes) :
    Satisfies ({n}.completed fq fr model upstream backend point base) rows := by
  intro row member
  have agrees (terms : Linear) (included : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
      eval ({n}.completed fq fr model upstream backend point base) terms = eval base terms := by
    apply eval_agrees
    intro term present
    exact outside fq fr model upstream backend point base term.1 (support row member term (included term present))
  change Square (eval ({n}.completed fq fr model upstream backend point base) row.a)
    (eval ({n}.completed fq fr model upstream backend point base) row.b)
  rw [agrees row.a (by intro term present; exact List.mem_append_left _ present),
    agrees row.b (by intro term present; exact List.mem_append_right _ present)]
  exact earlier row member
#print axioms outside
#print axioms rows_preserved
end ShielddSecurity.{name}
'''
    return name, _signature_audits(source)
