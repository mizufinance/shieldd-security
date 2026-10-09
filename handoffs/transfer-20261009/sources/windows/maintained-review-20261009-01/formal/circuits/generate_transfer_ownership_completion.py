"""Bounded exact local variable-window constructors from retained row plans.

Local division legality is deliberately explicit here. The whole variable-loop
constructor must derive it from its preceding curve invariant; this module
does not treat a desired target, scalar, or incoming row truth as a premise.
"""
from . import transfer_ownership_completion as completion
from .generate_hash_round import linear, _signature_audits


def lower_stage(stage):
    """Shared exact mixed-stage syntax for local and per-point constructors."""
    terms = []
    if stage['kind'] == 'square':
        input_lc, remainder = (linear(stage[key]) for key in ('input', 'remainder'))
        output = stage['output']
        terms.append(f'.compiler (.square {input_lc} {remainder} {output})')
        rows = [f'⟨{input_lc},[({output},1)] ++ {remainder}⟩']
    elif stage['kind'] == 'product':
        left, right, remainder = (linear(stage[key]) for key in ('left', 'right', 'remainder'))
        output, auxiliary = stage['output'], stage['auxiliary']
        terms.append(f'.compiler (.product {left} {right} {remainder} {output} {auxiliary})')
        rows = [f'⟨Compiler.subtract {left} {right},[({auxiliary},1)]⟩',
                f'⟨{left} ++ {right},[({auxiliary},1)] ++ scaleLinear 4 ([({output},1)] ++ {remainder})⟩']
    elif stage['kind'] == 'linear':
        input_lc, remainder = (linear(stage[key]) for key in ('input', 'remainder'))
        output = stage['output'];terms.append(f'.linear {input_lc} {remainder} {output}')
        rows = [f'⟨Compiler.subtract ([({output},1)] ++ {remainder}) {input_lc},[]⟩']
    else:
        numerator, denominator, remainder = (linear(stage[key]) for key in ('numerator', 'denominator', 'remainder'))
        q, p, a = (stage[key] for key in ('quotient', 'product', 'auxiliary'))
        terms.append(f'.quotient {numerator} {denominator} {remainder} {q} {p} {a}')
        rows = [f'⟨Compiler.subtract [({q},1)] {denominator},[({a},1)]⟩',
                f'⟨[({q},1)] ++ {denominator},[({a},1)] ++ scaleLinear 4 ([({p},1)] ++ {remainder})⟩',
                f'⟨Compiler.subtract ([({p},1)] ++ {remainder}) {numerator},[]⟩']
    if len(rows) != len(stage['rows']):
        raise completion.relation.RelationError('ownership completion emitted exact stage row count')
    return terms[0], rows


def generate(checked, extracted, window_offset=0, include_precompute=True, readonly_lcs=()):
    plan = completion.window_plan(checked, extracted, window_offset, include_precompute, readonly_lcs)
    prefix = 'RuntimeRnkWindow' if checked['metadata'].get('schema') == 'shieldd-transfer-rnk-dh-v1' else 'RuntimeOwnershipWindow'
    return render_plan(checked,extracted,plan,prefix)


def render_plan(checked,extracted,plan,prefix):
    """Neutral exact mixed-row syntax; schema acceptance stays in its caller."""
    import re
    if re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',prefix) is None:
        raise completion.relation.RelationError('local completion namespace')
    copy = checked['metadata']['constant_copy'];modulus = completion.relation.MODULUS
    raw = {row['row']: tuple(tuple((c, int(v, 16)) for c, v in row[key]) for key in ('a', 'b'))
           for row in extracted['selected_rows']}
    terms = [];expected = {}
    for stage in plan['stages']:
        term, rows = lower_stage(stage)
        terms.append(term);expected.update(zip(stage['rows'], rows))
    for index in plan['constant_rows']:expected[index] = '⟨[],[]⟩'
    if set(expected) != set(plan['local_rows']):
        raise completion.relation.RelationError('ownership completion entire local original coverage')
    terms.append('.compiler (.equal [] [])')
    name = prefix+f'{plan["window_index"]:03d}Completion'
    source = f'''import ShielddSecurity.GroupCircuitOrder
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Exact retained local row construction. Curve-derived division legality,
-- actual endpoint rows and whole/native/source joins remain separate.
def modulus : Nat := {modulus}
def kept : List Nat := {plan['protected']}
def originalRows : List Nat := {plan['local_rows']}
def ownedWrites : List Nat := {plan['writes']}
def rawRows : List Row := ['''+',\n'.join('⟨'+linear(raw[i][0])+','+linear(raw[i][1])+'⟩' for i in plan['local_rows'])+''']
def completionSteps : List GroupCircuitCompletion.Step := ['''+','.join(terms)+''']
def completeAssignment {F : Type} [Field F] (base : Nat → F) : Nat → F :=
  GroupCircuitCompletion.run base completionSteps
theorem completion_ordered : GroupCircuitCompletion.Topological kept [] completionSteps :=
  GroupCircuitOrder.checked_order kept [] completionSteps (by decide)
theorem original_coverage : ∀ actual ∈ rawRows, ∃ expected ∈ GroupCircuitCompletion.emitted completionSteps,
'''+f'''    Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  simp only [rawRows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with '''+' | '.join('rfl' for _ in plan['local_rows'])+'\n'
    for index in plan['local_rows']:
        source += f'''  · refine ⟨{expected[index]}, ?_, by decide, by decide⟩
    simp [completionSteps,GroupCircuitCompletion.emitted,GroupCircuitCompletion.Step.rows,
      CompilerCompletion.Step.rows,CompilerCompletion.squareRows,ScalarCompletion.productRows,
      GroupRowCompletion.quotientRows,CompilerLinearCompletion.rows,Compiler.subtract,scaleLinear]
'''
    source += f'''theorem local_rows_complete {{F : Type}} [Field F] [CharP F modulus]
    (base : Nat → F) (linked : base {copy} = base 0)
    (legal : GroupCircuitCompletion.Legal base completionSteps) :
    Satisfies (completeAssignment base) rawRows ∧
      (∀ column ∈ kept, completeAssignment base column = base column) :=
  GroupCircuitCompletion.original_rows_complete base completionSteps kept rawRows {copy}
    completion_ordered legal (by decide) (by decide) linked original_coverage
theorem protected_columns {{F : Type}} [Field F] (base : Nat → F) (column : Nat)
    (member : column ∈ kept) : completeAssignment base column = base column :=
  GroupCircuitCompletion.run_preserves base completionSteps kept [] completion_ordered column member
'''
    for export in ('completion_ordered', 'original_coverage', 'local_rows_complete', 'protected_columns'):
        source += '#print axioms '+export+'\n'
    return name, _signature_audits(source+f'end ShielddSecurity.{name}\n')
