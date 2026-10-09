"""Compose eight bounded actual ordinary EPK page certificates.

The folded prefix and canonical scalar construction are separate predecessors.
This constructor derives the 125-window native recurrence on one assignment;
it accepts no individual row satisfaction or desired output equality.
"""
from . import transfer_epk_fixed_program as full, transfer_fixed_spend as fixed
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits, signed


def generate(parent, pages, capsules, roles, extracted, scope_id):
    accepted = full.plan(parent, pages, capsules, roles, extracted, scope_id)
    chunks, bounds = accepted['chunks'], accepted['bounds']
    if (len(chunks) != 8 or
            [c['metadata']['window_start'] for c in chunks] != list(range(0, 126, 16)) or
            len(accepted['loop']['programs']) != 126):
        raise relation.RelationError('EPK full trace exact eight-page126 source inventory')
    stem = f'RuntimeTransferEpk{scope_id}Fixed'
    trace = [stem + f'TemplatePage{i:02d}Trace' for i in range(8)]
    joins = [stem + f'TemplatePage{i:02d}Join' for i in range(8)]
    ns = stem + 'TemplateOrdinaryTrace'
    copy, high = bounds['constant_copy'], bounds['high_start']
    d = signed(fixed.D)
    imports = ''.join(f'import ShielddSecurity.{m}\n' for m in trace + joins)
    source = imports + f'''import ShielddSecurity.GroupFixedTemplatePages
import ShielddSecurity.GroupFixedTemplateProgramAlignment
namespace ShielddSecurity.{ns}
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

def pages (n : Nat) : List (List GroupFixedTemplateTrace.Window) := [{','.join(p+'.windows n' for p in trace)}]
def windows (n : Nat) := (pages n).flatten
def segments (n : Nat) := [{','.join(p+'.segments n' for p in trace)}].flatten
def kept : List Nat := {joins[0]}.kept
def input : Linear × Linear := {trace[0]}.input
def base : Group.Point Int := {trace[0]}.base

theorem certified_bounds (n : Nat) : GroupFixedCircuitBounds.Certified {high} {copy}
    RuntimeTransferEpk{scope_id}FixedWindow001TemplateTrace.before (segments n) := by
  apply GroupFixedTemplatePages.certified_pages
'''
    for p in trace:
        source += f'  refine ⟨{p}.certified_bounds n, ?_⟩\n'
    source += '''  trivial

theorem aligned (n : Nat) : GroupFixedTemplateTrace.Aligned input base (windows n) := by
  apply GroupFixedTemplatePages.aligned_pages
'''
    for p in trace:
        source += f'  refine ⟨({p}.source_aligned n).1, ?_⟩\n'
    source += f'''  trivial

theorem checked (n : Nat) : ∀ window ∈ windows n,
    window.Checked {relation.MODULUS} {copy} {d} ∧ window.TableChecked {relation.MODULUS} := by
  apply GroupFixedTemplatePages.checked_pages
  intro page member
  simp only [pages,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with {' | '.join('rfl' for _ in trace)}
'''
    for p in trace:
        source += f'  · exact {p}.checked n\n'
    source += f'''
theorem segments_programs (n : Nat) : (segments n).map Prod.fst =
    (windows n).map GroupFixedTemplateTrace.Window.program := rfl

theorem fresh (n : Nat) : GroupFixedCircuitCompletion.Fresh []
    ((windows n).map GroupFixedTemplateTrace.Window.program) := by
  have result := GroupFixedCircuitBounds.bounded_fresh {high} {copy}
    RuntimeTransferEpk{scope_id}FixedWindow001TemplateTrace.before [] (segments n)
    (by intro row member; cases member) (certified_bounds n)
  rw [segments_programs] at result
  exact result

theorem program_aligned (n : Nat) : GroupFixedCircuitCompletion.Aligned input
    ((windows n).map GroupFixedTemplateTrace.Window.program) :=
  GroupFixedTemplateProgramAlignment.checked_alignment {relation.MODULUS} {copy} {d}
    (windows n) input base (aligned n) (by intro window member; exact (checked n window member).1)

theorem constructors {{F : Type}} [Field F] [CharP F {relation.MODULUS}]
    (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (({d} : Int) : F))
    (imaginarySquare : imaginary*imaginary = -1) (n : Nat) :
    ∀ window ∈ windows n, GroupFixedCircuitCompletion.LocalConstruct (({d} : Int) : F) {copy} window.program := by
  intro window member
  obtain ⟨page,present,inside⟩ := List.mem_flatten.mp member
  simp only [pages,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with {' | '.join('rfl' for _ in trace)}
'''
    for p in trace:
        source += f'  · exact {p}.constructors four imaginary nonSquare imaginarySquare n window inside\n'
    for theorem, target, call in (
            ('caller_protected', 'GroupFixedCircuitCompletion.Protected kept program', 'caller_protected'),
            ('bit_supports', '∀ term ∈ program.low ++ program.high, term.1 ∈ kept', 'bit_supports')):
        source += f'''
theorem {theorem} (n : Nat) : ∀ program ∈ (windows n).map GroupFixedTemplateTrace.Window.program,
    {target} := by
  intro program member
  obtain ⟨window,present,rfl⟩ := List.mem_map.mp member
  obtain ⟨page,inside,windowInside⟩ := List.mem_flatten.mp present
  simp only [pages,List.mem_cons,List.not_mem_nil,or_false] at inside
  rcases inside with {' | '.join('rfl' for _ in trace)}
'''
        for j in joins:
            source += f'  · exact {j}.{call} n window.program (List.mem_map_of_mem windowInside)\n'
    source += f'''
theorem actual_native_complete {{F : Type}} [Field F] [CharP F {relation.MODULUS}]
    {{J : Type}} [AddCommGroup J] (model : Group.StandardCurveModel J (({d} : Int) : F))
    (rho : Nat → F) (n : Nat) (acc generator : J)
    (one : rho 0 = 1) (linked : rho {copy} = rho 0) (four : (4 : F) ≠ 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare (({d} : Int) : F))
    (imaginarySquare : imaginary*imaginary = -1)
    (inputMeaning : GroupFixedCircuitCompletion.point rho input = model.coordinates acc)
    (baseMeaning : GroupFixedWindowTemplate.castPoint base = model.coordinates generator)
    (bits : ∀ program ∈ (windows n).map GroupFixedTemplateTrace.Window.program,
      eval rho program.low = (if program.lowBit then 1 else 0) ∧
      eval rho program.high = (if program.highBit then 1 else 0)) :
    let completed := GroupFixedCircuitCompletion.run rho ((windows n).map GroupFixedTemplateTrace.Window.program)
    Satisfies completed (GroupFixedCircuitCompletion.rows ((windows n).map GroupFixedTemplateTrace.Window.program)) ∧
    (∀ column ∈ kept, completed column = rho column) ∧
    GroupFixedCircuitCompletion.point completed (GroupFixedTemplateTrace.endpoint input (windows n)) =
      model.coordinates (acc + TransferWindows.digitsValue
        (((windows n).map (fun window => window.witness completed)).map GroupFixedWindows.fixedDigit) • generator) := by
  have inputSupports : ∀ term ∈ input.1 ++ input.2, term.1 ∈ kept := by
    have checked : (input.1 ++ input.2).all (fun term => decide (term.1 ∈ kept)) = true := by decide
    intro term member
    exact of_decide_eq_true (List.all_eq_true.mp checked term member)
  exact GroupFixedTemplateTrace.constructs_native {copy} {d} model rho
    (windows n) input base kept acc generator one linked four imaginary nonSquare imaginarySquare
    inputMeaning baseMeaning (constructors four imaginary nonSquare imaginarySquare n)
    (caller_protected n) inputSupports (bit_supports n) (fresh n) (program_aligned n) (aligned n)
    (by decide) (by decide) (checked n) bits
'''
    exports = ['certified_bounds', 'aligned', 'checked', 'segments_programs', 'fresh',
               'program_aligned', 'constructors', 'caller_protected', 'bit_supports', 'actual_native_complete']
    source += ''.join(f'#print axioms {e}\n' for e in exports)
    source += f'end ShielddSecurity.{ns}\n'
    return ns, _signature_audits(source)
