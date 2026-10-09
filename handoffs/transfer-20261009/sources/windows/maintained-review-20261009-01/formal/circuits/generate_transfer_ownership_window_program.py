"""Actual bounded variable-window adapters for the symbolic constructor rule.

Frames are finite column fences checked against actual owned writes and row
supports. They make no claim about compiler allocation provenance. The local
constructor derives row truth from the actual window proof; metadata alone
does not supply a proof or promote a diagnostic candidate.
"""
from . import transfer_ownership_completion as completion
from .generate_hash_round import linear, _signature_audits


def generate(checked, extracted, window_offset, readonly_lcs=()):
    if type(window_offset) is not int or not 0 <= window_offset < len(checked['windows']):
        raise completion.relation.RelationError('ownership typed bounded program selection')
    plan = completion.window_plan(checked, extracted, window_offset, False, readonly_lcs)
    observe = lambda value: checked['derived'][value[1]] if value[0] == 'source' else completion.canonical([(0,value[1])])
    window = checked['windows'][window_offset]
    input_point, output_point = tuple(map(observe,window[0])),tuple(map(observe,window[4]))
    prefix = 'RuntimeRnkWindow' if checked['metadata'].get('schema') == 'shieldd-transfer-rnk-dh-v1' else 'RuntimeOwnershipWindow'
    stem = prefix+f'{plan["window_index"]:03d}'; name = stem+'Program'
    folded = plan['window_index'] == 0
    if folded:
        constructor = stem+'FoldedCurveCompletion'
        runner = stem+'FoldedCompletion'
        rows = runner+'.rawRows'; steps = runner+'.completionSteps'
        coefficient = stem+'Point4Cones.coefficientD'
        if input_point != ((),((0,1),)):
            raise completion.relation.RelationError('ownership first program exact identity input')
    else:
        constructor = stem+'CurveCompletion'; runner = constructor
        rows = runner+'.rawRows'; steps = runner+'.steps'; coefficient=runner+'.d'
    # The first legacy arithmetic module includes the once-only native table
    # precomputation as well as the folded window. Those earlier rows are
    # constructed by NativePrecompute and preserved by the variable loop;
    # they are not rows owned by the folded window itself.
    prior = (stem+'NativePrecompute.firstRows ++ '+stem+'Point1Cones.rawRows ++ '+
             stem+'Point1Completion.quotientRaw') if folded else None
    prior_import = f'import ShielddSecurity.{stem}NativePrecompute\n' if folded else ''
    prior_definition = f'def priorRows : List Row := {prior}\n' if folded else ''
    coverage_rows = f'(priorRows ++ {rows})' if folded else rows
    coverage_target = 'priorRows ++ (program lowBit highBit).rows' if folded else '(program lowBit highBit).rows'
    origin = 22738
    low_writes = [column for column in plan['writes'] if column < origin]
    high_writes = [column for column in plan['writes'] if column >= origin and column != checked['metadata']['constant_copy']]
    if not low_writes or not high_writes or len(set(plan['writes'])) != len(plan['writes']):
        raise completion.relation.RelationError('ownership program exact two finite write fences')
    before = (min(low_writes),min(high_writes)); after = (max(low_writes)+1,max(high_writes)+1)
    points = [tuple(map(observe,checked['points'][role])) for role in ('base','twice','triple')]
    def pair(terms):return '('+linear(terms[0])+','+linear(terms[1])+')'
    source = f'''import ShielddSecurity.{constructor}
{prior_import}\
import ShielddSecurity.{stem}
import ShielddSecurity.GroupVariableCircuitCompletion
import ShielddSecurity.GroupFixedCircuitBounds
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
{prior_definition}\
def tables : GroupVariableCircuitCompletion.Tables := ⟨{','.join(pair(point) for point in points)}⟩
def beforeFrame : GroupFixedCircuitBounds.Frame := ⟨{before[0]},{before[1]}⟩
def afterFrame : GroupFixedCircuitBounds.Frame := ⟨{after[0]},{after[1]}⟩
def program (lowBit highBit : Bool) : GroupFixedCircuitCompletion.Program :=
  ⟨{steps},{rows},{pair(input_point)},{pair(output_point)},
    {constructor}.low,{constructor}.high,lowBit,highBit⟩
theorem original_rows_covered (lowBit highBit : Bool) :
    ∀ row ∈ {stem}.rawRows, row ∈ {coverage_target} := by
  have checked : {stem}.rawRows.all (fun row => decide (row ∈ {coverage_rows})) = true := by decide
  intro row member
  exact of_decide_eq_true (List.all_eq_true.mp checked row member)
'''
    # Later curve modules use the exact selector namespace for their low/high
    # declarations. Keeping those original definitions avoids an invented bit
    # observation or a new source handle.
    if not folded:
        selector = stem+f'Point{4+3*window_offset}SelectorCompletion'
        source = source.replace(constructor+'.low',selector+'.low').replace(constructor+'.high',selector+'.high')
    source += f'''theorem checked_bounds (lowBit highBit : Bool) :
    GroupFixedCircuitBounds.checkLocal {origin} {checked['metadata']['constant_copy']}
      beforeFrame afterFrame (program lowBit highBit) = true := by
  cases lowBit <;> cases highBit <;> decide
theorem caller_protected {{F : Type}} [Field F] (base : Nat → F) (lowBit highBit : Bool)
    (column : Nat) (member : column ∈ {runner}.kept) :
    (program lowBit highBit).build base column = base column := by
'''
    if folded:
        source += f'''  exact {runner}.protected_columns base column member
'''
    else:
        source += f'''  change GroupCircuitCompletion.run base {runner}.steps column = base column
  rw [{runner}.completion_factor]
  exact {runner}.protected_columns base column member
'''
    source += f'''theorem local_constructor {{F : Type}} [Field F] [CharP F {runner}.modulus]
    (imaginary : F) (nonSquare : Group.NoUnitSquare ({coefficient} : F))
    (imaginarySquare : imaginary*imaginary = -1) (lowBit highBit : Bool) :
    GroupVariableCircuitCompletion.LocalConstruct ({coefficient} : F)
      {checked['metadata']['constant_copy']} tables (program lowBit highBit) := by
  intro base one linked incoming curved lowValue highValue
'''
    if folded:
        source += f'''  have result := {constructor}.actual_window_complete base one linked lowBit highBit lowValue highValue
    curved.1 curved.2.1 curved.2.2
  simpa only [program,GroupFixedCircuitCompletion.Program.build,{runner}.completeAssignment,
    GroupFixedCircuitCompletion.point,{constructor}.output,eval,Int.cast_one,one_mul,add_zero] using result
'''
    else:
        first = stem+f'Point{2+3*window_offset}Completion'; add = stem+f'Point{4+3*window_offset}Completion'
        source += f'''  have result := {constructor}.actual_window_complete base one linked imaginary nonSquare imaginarySquare
    lowBit highBit incoming lowValue highValue curved.1 curved.2.1 curved.2.2
  simpa only [program,GroupFixedCircuitCompletion.Program.build,{runner}.completion_factor,
    GroupFixedCircuitCompletion.point,{add}.outputPoint,GroupQuotientPairCompletion.point,
    {add}.x,{add}.y,eval,Int.cast_one,one_mul,add_zero] using result
'''
    source += f'''#print axioms original_rows_covered
#print axioms checked_bounds
#print axioms caller_protected
#print axioms local_constructor
end ShielddSecurity.{name}
'''
    return name,_signature_audits(source)
