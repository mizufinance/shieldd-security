"""Optional exact balance129 Program overrides; full local fallback unchanged.

The root consumer must qualify the real template1 Program and generic helper
before compiling these leaves. This renderer never reads the ordinary relation
or infers qualification from its strict metadata/row matching.
"""
from . import transfer_balance_variable_renaming as matching
from . import transfer_balance_variable_program as plans
from . import generate_transfer_balance_variable_completion as local
from . import generate_transfer_balance_variable_sequence as sequence
from .generate_transfer_ownership_completion import lower_stage
from .generate_hash_round import linear,_signature_audits


def _permutation_expression(pairs):
    forward=dict(pairs)
    if len(forward)!=len(pairs) or set(forward)!=set(forward.values()):
        raise matching.relation.RelationError('balance renderer finite permutation required')
    visited=set();swaps=[]
    for start in sorted(forward):
        if start in visited:continue
        cycle=[];current=start
        while current not in visited:
            visited.add(current);cycle.append(current);current=forward[current]
        if current!=start:raise matching.relation.RelationError('balance renderer closed finite cycles')
        swaps.extend((start,column) for column in cycle[1:])
    # trans applies the left permutation first. The successive root swaps
    # implement a->b->c->a, including overlapping source/target supports.
    expression='(Equiv.refl Nat)'
    for a,b in swaps:expression=f'({expression}.trans (Equiv.swap {a} {b}))'
    return expression


def _source(accepted,item,match,kept):
    source=local.PREFIX+f'{match["source_window"]:03d}Program'
    stem=local.PREFIX+f'{item["index"]:03d}'
    name=stem+'Program';page=accepted['checked']['chunks'][item['page_ordinal']]
    observe=lambda value:page['derived'][value[1]] if value[0]=='source' else matching.completion.canonical([(0,value[1])])
    point=lambda values:'('+','.join(linear(observe(v)) for v in values)+')'
    tables=','.join(point(page['points'][role]) for role in ('base','twice','triple'))
    bits=[linear(observe(v)) for v in item['bits']]
    # The qualified point-materialization constructor includes a zero equality
    # for its unoutlined constant-link row. Retain that identity step at each
    # material boundary when transporting the constructor's exact stage list.
    # The genuine runtime stages, physical rows, and owned writes stay exact.
    plan=item['plan']
    boundaries={group['material_end'] for group in plan['point_groups']}
    if len(boundaries)!=3 or any(not 0<end<=len(plan['stages']) for end in boundaries):
        raise matching.relation.RelationError('balance transport three materialization boundaries')
    lowered=[]
    for index,stage in enumerate(plan['stages'],1):
        lowered.append(lower_stage(stage)[0])
        if index in boundaries:
            lowered.append('.compiler (.equal [] [])')
    stages=','.join(lowered)
    rows=plans._rows(accepted['selections'][item['page_ordinal']],item['rows'])
    raw=','.join('⟨'+linear(row[0])+','+linear(row[1])+'⟩' for row in rows.values())
    copy=page['metadata']['constant_copy'];modulus=matching.relation.MODULUS
    before=item['before_frame'];after=item['after_frame']
    source_body=f'''import ShielddSecurity.{source}
import ShielddSecurity.GroupCircuitRenaming
import ShielddSecurity.GroupFixedCircuitBounds
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Exact genuine balance129 parent {accepted['parent_sha256']}.
-- Source-only optional constructor transport; old per-window fallback retained.
def modulus : Nat := {modulus}
def d : Int := RuntimeBalanceVariableWindow001CurveCompletion.d
def permutation : Nat ≃ Nat := {_permutation_expression(match['columns'])}
def columns (column : Nat) : Nat := permutation column
def stages : List GroupCircuitCompletion.Step := [{stages}]
def actualRows : List Row := [{raw}]
def tables : GroupVariableCircuitCompletion.Tables := ⟨{tables}⟩
def beforeFrame : GroupFixedCircuitBounds.Frame := ⟨{before[0]},{before[1]}⟩
def afterFrame : GroupFixedCircuitBounds.Frame := ⟨{after[0]},{after[1]}⟩
def program (lowBit highBit : Bool) : GroupFixedCircuitCompletion.Program :=
  ⟨stages,actualRows,{point(item['incoming'])},{point(item['outgoing'])},{bits[0]},{bits[1]},lowBit,highBit⟩
def mappedProgram (lowBit highBit : Bool) :=
  GroupCircuitRenaming.program columns ({source}.program lowBit highBit)
theorem columns_injective : Function.Injective columns := permutation.injective
theorem fields_checked (lowBit highBit : Bool) :
    (program lowBit highBit).stages = (mappedProgram lowBit highBit).stages ∧
    (program lowBit highBit).input = (mappedProgram lowBit highBit).input ∧
    (program lowBit highBit).output = (mappedProgram lowBit highBit).output ∧
    (program lowBit highBit).low = (mappedProgram lowBit highBit).low ∧
    (program lowBit highBit).high = (mappedProgram lowBit highBit).high ∧
    tables = GroupCircuitRenaming.tables columns {source}.tables := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
theorem original_rows_covered (lowBit highBit : Bool) :
    ∀ row ∈ actualRows, row ∈ (mappedProgram lowBit highBit).rows := by
  have checked : actualRows.all (fun row => decide (row ∈ (mappedProgram false false).rows)) = true := by decide
  intro row member
  exact of_decide_eq_true (List.all_eq_true.mp checked row member)
theorem checked_bounds (lowBit highBit : Bool) :
    GroupFixedCircuitBounds.checkLocal 22738 {copy} beforeFrame afterFrame
      (program lowBit highBit) = true := by
  cases lowBit <;> cases highBit <;> decide
theorem outside {{F : Type}} [Field F] (base : Nat → F) (lowBit highBit : Bool)
    (column : Nat) (fresh : column ∉ GroupCircuitSequenceCompletion.writes stages) :
    (program lowBit highBit).build base column = base column :=
  GroupCircuitSequenceCompletion.run_preserves base stages column fresh
theorem local_constructor {{F : Type}} [Field F] [CharP F modulus]
    (imaginary : F) (nonSquare : Group.NoUnitSquare (d : F))
    (imaginarySquare : imaginary*imaginary = -1) (lowBit highBit : Bool) :
    GroupVariableCircuitCompletion.LocalConstruct (d : F) {copy} tables (program lowBit highBit) := by
  have fields := fields_checked lowBit highBit
  have reused := GroupCircuitRenaming.local_constructor columns columns_injective
    (by decide) {copy} (by decide) (d : F) {source}.tables ({source}.program lowBit highBit)
    ({source}.local_constructor imaginary nonSquare imaginarySquare lowBit highBit)
  intro base one linked incoming curved low high
  have sourceIncoming : Group.OnCurve (d : F)
      (GroupFixedCircuitCompletion.point base (mappedProgram lowBit highBit).input) := by
    rw [← fields.2.1]
    exact incoming
  have sourceCurved : GroupVariableCircuitCompletion.Curved (d : F)
      (GroupCircuitRenaming.tables columns {source}.tables) base := by
    rw [← fields.2.2.2.2.2]
    exact curved
  have sourceLow : eval base (mappedProgram lowBit highBit).low = (if lowBit then 1 else 0) := by
    rw [← fields.2.2.2.1]
    exact low
  have sourceHigh : eval base (mappedProgram lowBit highBit).high = (if highBit then 1 else 0) := by
    rw [← fields.2.2.2.2.1]
    exact high
  have completed := reused base one linked sourceIncoming sourceCurved sourceLow sourceHigh
  have build : (program lowBit highBit).build base = (mappedProgram lowBit highBit).build base :=
    congrArg (GroupCircuitCompletion.run base) fields.1
  constructor
  · intro row member
    rw [build]
    exact completed.1 row (original_rows_covered lowBit highBit row member)
  · rw [build,fields.2.2.1]
    exact completed.2
theorem local_formula {{F : Type}} [Field F] [CharP F modulus]
    (imaginary : F) (nonSquare : Group.NoUnitSquare (d : F))
    (imaginarySquare : imaginary*imaginary = -1) (lowBit highBit : Bool) :
    GroupVariableCircuitNative.LocalFormula (d : F) {copy} tables (program lowBit highBit) := by
  have fields := fields_checked lowBit highBit
  have reused := GroupCircuitRenaming.local_formula columns columns_injective
    (by decide) {copy} (by decide) (d : F) {source}.tables ({source}.program lowBit highBit)
    ({source}.local_formula imaginary nonSquare imaginarySquare lowBit highBit)
  unfold GroupVariableCircuitNative.LocalFormula at reused ⊢
  simpa only [GroupFixedCircuitCompletion.Program.build,fields.1,fields.2.1,
    fields.2.2.1,fields.2.2.2.1,fields.2.2.2.2.1,fields.2.2.2.2.2,
    program,mappedProgram,GroupCircuitRenaming.program] using reused
def sequenceKept : List Nat := {kept}
theorem sequence_protected (lowBit highBit : Bool) :
    GroupFixedCircuitCompletion.Protected sequenceKept (program lowBit highBit) := by
  have checked : stages.all (fun stage => GroupCircuitOrder.checkOutside sequenceKept stage.writes) = true := by decide
  intro stage member column present written
  exact (of_decide_eq_true
    (List.all_eq_true.mp (List.all_eq_true.mp checked stage member) column written)) present
'''
    for export in ('columns_injective','fields_checked','original_rows_covered','checked_bounds','outside','local_constructor','local_formula','sequence_protected'):
        source_body+='#print axioms '+export+'\n'
    return name,_signature_audits(source_body+f'end ShielddSecurity.{name}\n')


def generate(parent,pages,digest,signed,asset_base,extracted,readonly_lcs=(),*,compiler_origin=22738):
    if compiler_origin!=22738:raise matching.relation.RelationError('balance original compiler allocation origin')
    accepted=plans.plan(parent,pages,digest,signed,asset_base,extracted,readonly_lcs,compiler_origin=compiler_origin)
    kept=sequence._kept(accepted,signed);result={};fallback=[]
    for item in accepted['programs']:
        if item['index']<2:
            name,body=local.render_program(accepted['checked']['chunks'][item['page_ordinal']],
                accepted['selections'][item['page_ordinal']],item['window_offset'],readonly_lcs,
                compiler_origin=compiler_origin,sequence_kept=kept)
        else:
            try:
                match=matching._pair(accepted,1,item['index'])
                name,body=_source(accepted,item,match,kept)
            except matching.relation.RelationError as error:
                fallback.append(dict(window=item['index'],reason=str(error)))
                name,body=local.render_program(accepted['checked']['chunks'][item['page_ordinal']],
                    accepted['selections'][item['page_ordinal']],item['window_offset'],readonly_lcs,
                    compiler_origin=compiler_origin,sequence_kept=kept)
        if name in result:raise matching.relation.RelationError('balance renaming unique actual Program namespace')
        result[name]=body
    result.update(sequence.render_modules(accepted,kept,compiler_origin,signed))
    return dict(modules=result,fallback=fallback,source_only=True,qualification=False,certification=False,
        ordinary_replays=0,parent_sha256=accepted['parent_sha256'],raw_page_sha256=accepted['raw_page_sha256'],
        scope='Optional balance129 proof source overrides only. Exact helper/template named kernel receipts must be bound by root before kernel instantiation. Existing per-window fallback and all shared/native/frame joins retained; no H reuse.')
