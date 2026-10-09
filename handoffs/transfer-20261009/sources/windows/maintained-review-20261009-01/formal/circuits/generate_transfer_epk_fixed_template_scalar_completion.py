"""Construct the folded prefix and ordinary125 on one common assignment.

Only source scalar-bit meanings are inputs. The first coordinate, every window
row predicate and the final scalar multiple are derived by the constructors.
Canonical scalar ingress and the caller/SDK boundary remain separate joins.
"""
from . import transfer_epk_fixed_program as full
from . import transfer_fixed_spend as fixed, transfer_relation as relation
from .generate_hash_round import _signature_audits, signed
from .transfer_balance_rows import source_index


def generate(parent, pages, capsules, roles, extracted, scope_id):
    accepted = full.plan(parent, pages, capsules, roles, extracted, scope_id)
    if (len(accepted['chunks']) != 8 or
            [c['metadata']['window_start'] for c in accepted['chunks']] != list(range(0, 126, 16)) or
            len(accepted['loop']['programs']) != 126):
        raise relation.RelationError('EPK scalar completion requires exact eight-page126 inventory')
    frames = accepted['bounds']['frames']
    start = accepted['scalar']['bit_start']
    columns = set()
    for index in range(1, 126):
        page = accepted['chunks'][index // 16]
        for axis in range(2):
            handle = source_index(page['metadata']['bits'][2*index + axis])
            terms = page['observed'].get(handle)
            if terms != ((start + 2*index + axis, 1),):
                raise relation.RelationError('EPK scalar completion exact250 ordinary bit supports')
            columns.update(column for column, _ in terms)
    columns = sorted(columns)
    if len(frames) != 126 or columns != list(range(start + 2, start + 252)):
        raise relation.RelationError('EPK scalar completion exact250 ordinary bit supports')
    copy, upper = accepted['bounds']['constant_copy'], accepted['bounds']['high_start']
    d = signed(fixed.D)
    trace = f'RuntimeTransferEpk{scope_id}FixedTemplateOrdinaryTrace'
    prior = f'RuntimeTransferEpk{scope_id}FixedTemplateOrdinaryPrior'
    scalar = f'RuntimeTransferEpk{scope_id}FixedTemplateScalarTrace'
    first = f'RuntimeTransferEpk{scope_id}FixedWindow000'
    constructor = first + 'TemplatePrefix'
    before = f'RuntimeTransferEpk{scope_id}FixedWindow001TemplateTrace.before'
    ns = f'RuntimeTransferEpk{scope_id}FixedTemplateScalarCompletion'
    low = '(encodeBits 252 n)[0]?.getD false'
    high = '(encodeBits 252 n)[1]?.getD false'
    source = f'''import ShielddSecurity.{scalar}
import ShielddSecurity.{prior}
import ShielddSecurity.{constructor}
namespace ShielddSecurity.{ns}
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def bitColumns : List Nat := List.range' {start+2} 250

theorem prefix_bits_protected (low high : Bool) :
    GroupFixedCircuitCompletion.Protected bitColumns ({constructor}.program low high) := by
  have checked : ({constructor}.program false false).stages.all (fun stage =>
      stage.writes.all (fun column => decide (column < {start+2} ∨ {start+252} ≤ column))) = true := by decide
  intro stage member column present written
  have outside : column < {start+2} ∨ {start+252} ≤ column := of_decide_eq_true
    (List.all_eq_true.mp (List.all_eq_true.mp checked stage member) column written)
  simp only [bitColumns,List.mem_range',Nat.one_mul] at present
  obtain ⟨index,bound,equality⟩ := present
  omega

theorem ordinary_bit_supports (n : Nat) :
    ∀ program ∈ ({trace}.windows n).map GroupFixedTemplateTrace.Window.program,
      ∀ term ∈ program.low ++ program.high, term.1 ∈ bitColumns := by
  have checked : ({trace}.windows n).all (fun window =>
      (window.program.low ++ window.program.high).all (fun term => decide ({start+2} ≤ term.1 ∧ term.1 < {start+252}))) = true := by
    change ({trace}.windows 0).all (fun window =>
      (window.program.low ++ window.program.high).all (fun term => decide ({start+2} ≤ term.1 ∧ term.1 < {start+252}))) = true
    decide
  intro program member term present
  obtain ⟨window,inside,rfl⟩ := List.mem_map.mp member
  have bounds : {start+2} ≤ term.1 ∧ term.1 < {start+252} := of_decide_eq_true
    (List.all_eq_true.mp (List.all_eq_true.mp checked window inside) term present)
  simp only [bitColumns,List.mem_range',Nat.one_mul]
  exact ⟨term.1 - {start+2},by omega,by omega⟩

theorem prefix_rows_covered (low high : Bool) :
    GroupFixedCircuitBounds.RowsCovered {upper} {copy} {before} {first}.rawRows :=
  ({constructor}.checked_bounds low high).2.1

theorem actual_native_scalar_complete {{F : Type}} [Field F] [CharP F {relation.MODULUS}]
    {{J : Type}} [AddCommGroup J] (model : Group.StandardCurveModel J (({d} : Int) : F))
    (rho : Nat → F) (n : Nat) (generator : J) (bound : n < 2 ^ 252)
    (one : rho 0 = 1) (linked : rho {copy} = rho 0) (four : (4 : F) ≠ 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare (({d} : Int) : F))
    (imaginarySquare : imaginary*imaginary = -1)
    (baseMeaning : ({first}.base : Group.Point F) = model.coordinates generator)
    (lowValue : eval rho {first}.low = if {low} then 1 else 0)
    (highValue : eval rho {first}.high = if {high} then 1 else 0)
    (bits : ∀ program ∈ ({trace}.windows n).map GroupFixedTemplateTrace.Window.program,
      eval rho program.low = (if program.lowBit then 1 else 0) ∧
      eval rho program.high = (if program.highBit then 1 else 0)) :
    let firstAssignment := ({constructor}.program ({low}) ({high})).build rho
    let completed := GroupFixedCircuitCompletion.run firstAssignment
      (({trace}.windows n).map GroupFixedTemplateTrace.Window.program)
    Satisfies completed ({first}.rawRows ++ GroupFixedCircuitCompletion.rows
      (({trace}.windows n).map GroupFixedTemplateTrace.Window.program)) ∧
    (∀ column, column ∈ {constructor}.kept → column ∈ {trace}.kept → completed column = rho column) ∧
    GroupFixedCircuitCompletion.point completed
      (GroupFixedTemplateTrace.endpoint {trace}.input ({trace}.windows n)) =
      model.coordinates (n • generator) := by
  let firstAssignment := ({constructor}.program ({low}) ({high})).build rho
  let completed := GroupFixedCircuitCompletion.run firstAssignment
    (({trace}.windows n).map GroupFixedTemplateTrace.Window.program)
  have initial := {constructor}.actual_native_prefix model generator rho one linked
    imaginary nonSquare imaginarySquare ({low}) ({high}) lowValue highValue baseMeaning
  have oneFirst : firstAssignment 0 = 1 := (initial.2.1 0 (by decide)).trans one
  have linkedFirst : firstAssignment {copy} = firstAssignment 0 := by
    calc
      firstAssignment {copy} = rho {copy} := initial.2.1 {copy} (by decide)
      _ = rho 0 := linked
      _ = firstAssignment 0 := (initial.2.1 0 (by decide)).symm
  have bitsFirst : ∀ program ∈ ({trace}.windows n).map GroupFixedTemplateTrace.Window.program,
      eval firstAssignment program.low = (if program.lowBit then 1 else 0) ∧
      eval firstAssignment program.high = (if program.highBit then 1 else 0) := by
    intro program member
    have equal (lc : Linear) (inside : ∀ term ∈ lc, term ∈ program.low ++ program.high) :
        eval firstAssignment lc = eval rho lc := by
      apply eval_agrees
      intro term present
      exact GroupCircuitOrder.run_outside rho ({constructor}.program ({low}) ({high})).stages term.1
        (by
          intro stage written
          exact prefix_bits_protected ({low}) ({high}) stage written term.1
            (ordinary_bit_supports n program member term (inside term present)))
    exact ⟨(equal _ (by intro term present; exact List.mem_append_left _ present)).trans (bits program member).1,
      (equal _ (by intro term present; exact List.mem_append_right _ present)).trans (bits program member).2⟩
  have inputMeaning : GroupFixedCircuitCompletion.point firstAssignment {trace}.input =
      model.coordinates (GroupFixedWindows.fixedDigit ({scalar}.firstWitness (F := F) n) • generator) := by
    change {first}.output firstAssignment = _
    simpa only [{scalar}.firstWitness,GroupFixedWindows.fixedDigit] using initial.2.2.1
  have nextMeaning : GroupFixedWindowTemplate.castPoint {trace}.base = model.coordinates (4 • generator) := by
    change ({first}.nextBase : Group.Point F) = _
    exact initial.2.2.2
  have done := {prior}.actual_native_complete_prior model firstAssignment n
    (GroupFixedWindows.fixedDigit ({scalar}.firstWitness (F := F) n) • generator) (4 • generator)
    {first}.rawRows (prefix_rows_covered ({low}) ({high})) initial.1 oneFirst linkedFirst
    four imaginary nonSquare imaginarySquare inputMeaning nextMeaning bitsFirst
  have scalarValue := GroupFixedTemplateScalarDigits.folded_tail_value
    ({scalar}.firstWitness (F := F) n) (({trace}.windows n).map (fun window => window.witness completed))
    generator 252 n ({scalar}.actual_word completed n) bound
  refine ⟨done.1,?_,done.2.2.trans (congrArg model.coordinates scalarValue)⟩
  intro column firstKept ordinaryKept
  exact (done.2.1 column ordinaryKept).trans (initial.2.1 column firstKept)

#print axioms prefix_bits_protected
#print axioms ordinary_bit_supports
#print axioms prefix_rows_covered
#print axioms actual_native_scalar_complete
end ShielddSecurity.{ns}
'''
    return ns, _signature_audits(source)
