"""Construct the actual Point<Var>::add shared inverse and original rows.

Only a rechecked real-ingress plan reaches this renderer. Field/curve contracts
are explicit; intermediate products, reciprocal and outputs are constructed.
The legacy affine-window renderer keeps its existing default bytes.
"""
import re
from . import transfer_balance_shared_add as shared, transfer_balance_final_add as final
from . import transfer_relation as relation
from .generate_transfer_ownership_completion import lower_stage
from .generate_hash_round import linear, signed, _signature_audits
from .transfer_balance_rows import canonical


def _recheck(plan):
    if not isinstance(plan, dict) or plan.get('lowering') != 'point_shared_inverse':
        raise relation.RelationError('final shared inverse exact retained plan')
    protected = plan.get('protected')
    if not isinstance(protected, list) or len(protected) > 4096 or protected != sorted(set(protected)):
        raise relation.RelationError('final shared inverse bounded protected inventory')
    for column in protected:
        relation.natural(column, 262144)
    rows = plan.get('selected_rows')
    if not isinstance(rows, list) or not 1 <= len(rows) <= 256:
        raise relation.RelationError('final shared inverse bounded original row plan')
    matcher = shared.Matcher(plan.get('roles'))
    for row in rows:
        matcher.observe(row)
    checked = matcher.finish(plan.get('identity', {}), tuple(((c, 1),) for c in protected))
    for key in ('lowering', 'parents', 'roles', 'signed', 'inverse', 'plus', 'minus', 'cross',
                'diagonal', 'stages', 'writes', 'protected', 'selected_rows'):
        if checked[key] != plan.get(key):
            raise relation.RelationError('final shared inverse retained plan changed: ' + key)
    products = [s for s in checked['stages'] if s['kind'] == 'product']
    if [s['role'] for s in products] != list(shared.PRODUCT_ORDER):
        raise relation.RelationError('final shared inverse exact source product sequence')
    if len([s for s in checked['stages'] if s['kind'] == 'quotient']) != 1:
        raise relation.RelationError('final shared inverse single reciprocal constructor')
    return checked, matcher


def render_plan(plan, *, namespace='RuntimeTransferBalanceFinalAddCompletion'):
    if not isinstance(namespace, str) or not re.fullmatch('[A-Za-z][A-Za-z0-9_]*', namespace):
        raise relation.RelationError('final shared inverse Lean namespace')
    checked, matcher = _recheck(plan)
    stages = checked['stages']
    reciprocal = next(s for s in stages if s['kind'] == 'quotient')
    split = stages.index(reciprocal)
    lowered = [lower_stage(s) for s in stages]
    pre, post = stages[:split], stages[split+1:]
    writes = [c for s in stages for c in ([s['output'], s['auxiliary']] if s['kind'] == 'product'
              else [s['quotient'], s['product'], s['auxiliary']])]
    expected = {i: row for stage, (_, rows) in zip(stages, lowered) for i, row in zip(stage['rows'], rows)}
    raw = {r['row']: tuple(tuple((c, int(v, 16)) for c, v in r[k]) for k in ('a', 'b'))
           for r in checked['selected_rows']}
    constant = (canonical([(0, 1), (200692, -1)]), ())
    links = [i for i, row in raw.items() if row == constant]
    if len(links) != 1:
        raise relation.RelationError('final shared inverse exact constant link')
    expected[links[0]] = '⟨[],[]⟩'
    if set(expected) != set(raw) or sorted(writes) != checked['writes']:
        raise relation.RelationError('final shared inverse complete row/write coverage')
    term = lambda stage: lower_stage(stage)[0]
    source = f'''import ShielddSecurity.GroupCircuitSequenceCompletion
import ShielddSecurity.CompilerSignedCompletion
import ShielddSecurity.GroupSignedPoint
import ShielddSecurity.TransferSubgroup
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{namespace}
-- Exact group.rs Point<F>::add: ONE shared inverse, separate cross products.
-- Genuine source/native/frame associations remain preceding-constructor joins.
def modulus : Nat := {relation.MODULUS}
def d : Int := {signed(final.D)}
def kept : List Nat := {checked['protected']}
def ownedWrites : List Nat := {writes}
def preSteps : List GroupCircuitCompletion.Step := [{','.join(map(term, pre))}]
def inverseStep : GroupCircuitCompletion.Step := {term(reciprocal)}
def postSteps : List GroupCircuitCompletion.Step := [{','.join(map(term, post))},.compiler (.equal [] [])]
def steps : List GroupCircuitCompletion.Step := preSteps ++ [inverseStep] ++ postSteps
def preRows : List Row := GroupCircuitCompletion.emitted preSteps
def expectedRows : List Row := GroupCircuitCompletion.emitted steps
def originalIndices : List Nat := {sorted(raw)}
def rawRows : List Row := [{','.join('⟨'+linear(raw[i][0])+','+linear(raw[i][1])+'⟩' for i in sorted(raw))}]
def negative : Linear := {linear(checked['roles']['negative'])}
def unsignedX : Linear := {linear(checked['roles']['unsigned'][0])}
def unsignedY : Linear := {linear(checked['roles']['unsigned'][1])}
def blindedX : Linear := {linear(checked['roles']['blinded'][0])}
def blindedY : Linear := {linear(checked['roles']['blinded'][1])}
def signedX : Linear := {linear(checked['signed'][0])}
def signedY : Linear := {linear(checked['signed'][1])}
def plus : Linear := {linear(checked['plus'])}
def minus : Linear := {linear(checked['minus'])}
def inverse : Linear := {linear(checked['inverse'])}
def unsignedPoint {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F := ⟨eval rho unsignedX,eval rho unsignedY⟩
def blindedPoint {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F := ⟨eval rho blindedX,eval rho blindedY⟩
def signedPoint {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F := ⟨eval rho signedX,eval rho signedY⟩
def preAssignment {{F : Type}} [Field F] (base : Nat → F) : Nat → F := GroupCircuitCompletion.run base preSteps
def completeAssignment {{F : Type}} [Field F] (base : Nat → F) : Nat → F := GroupCircuitCompletion.run base steps
def outputPoint {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F :=
  ⟨eval rho {linear(checked['roles']['output'][0])},eval rho {linear(checked['roles']['output'][1])}⟩
theorem ordered : GroupCircuitCompletion.Topological kept [] steps :=
  GroupCircuitOrder.checked_order kept [] steps (by decide)
private theorem pre_ordered : GroupCircuitCompletion.Topological kept [] preSteps :=
  GroupCircuitOrder.checked_order kept [] preSteps (by decide)
theorem writes_exact : GroupCircuitSequenceCompletion.writes steps = ownedWrites := by decide
theorem outside {{F : Type}} [Field F] (base : Nat → F) (column : Nat)
    (excluded : column ∉ ownedWrites) : completeAssignment base column = base column := by
  exact GroupCircuitSequenceCompletion.run_preserves base steps column (by rw [writes_exact]; exact excluded)
theorem outside_eval {{F : Type}} [Field F] (base : Nat → F) (terms : Linear)
    (excluded : ∀ term ∈ terms, term.1 ∉ ownedWrites) :
    eval (completeAssignment base) terms = eval base terms := by
  apply eval_agrees
  intro term member
  exact outside base term.1 (excluded term member)
theorem preserves_earlier_rows {{F : Type}} [Field F] (base : Nat → F) (prior : List Row)
    (constructed : Satisfies base prior)
    (excluded : ∀ row ∈ prior, ∀ term ∈ row.a ++ row.b, term.1 ∉ ownedWrites) :
    Satisfies (completeAssignment base) prior := by
  apply GroupCircuitSequenceCompletion.preserves_rows base steps prior constructed
  intro row member term present
  rw [writes_exact]
  exact excluded row member term present
theorem pre_rows {{F : Type}} [Field F] (base : Nat → F) : Satisfies (preAssignment base) preRows := by
  apply GroupCircuitCompletion.run_constructs base preSteps kept pre_ordered
  simp [preSteps,GroupCircuitCompletion.Legal,GroupCircuitCompletion.Step.Legal,CompilerCompletion.Step.Legal]
theorem pre_preserves {{F : Type}} [Field F] (base : Nat → F) (terms : Linear)
    (included : ∀ term ∈ terms, term.1 ∈ kept) : eval (preAssignment base) terms = eval base terms := by
  apply eval_agrees
  intro term member
  exact GroupCircuitCompletion.run_preserves base preSteps kept [] pre_ordered term.1 (included term member)
private theorem four_nonzero {{F : Type}} [Field F] [CharP F modulus] : (4 : F) ≠ 0 := by
  intro zero
  have impossible : (4 : Nat) = 0 := bounded_cast_injective (F := F) (p := modulus)
    (by decide) (by decide) (by simpa using zero)
  omega
'''
    by_role = {s['role']: s for s in stages}
    inverse_product = dict(left=checked['inverse'], right=matcher.inverse_denominator,
                           auxiliary=reciprocal['auxiliary'], output=reciprocal['product'])
    for role in (*shared.PRODUCT_ORDER, 'inverseProduct'):
        left, right = matcher.requests[role]
        output = matcher.products[role]['output']
        for suffix, terms in (('Left', left), ('Right', right), ('Output', output)):
            source += f'def {role}{suffix} : Linear := {linear(terms)}\n'
        for tag, rows in ([('pre', 'preRows'), ('full', 'expectedRows')] if role in [s['role'] for s in pre]
                          else [('full', 'expectedRows')]):
            stage = inverse_product if role == 'inverseProduct' else by_role[role]
            source += f'''private theorem {role}_{tag} {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (completed : Satisfies rho {rows}) :
    eval rho {role}Output = eval rho {role}Left * eval rho {role}Right := by
  have calculated := Compiler.checked_product_sound rho {rows}
    {linear(stage['left'])} {linear(stage['right'])} {linear(output)} [({stage['auxiliary']},1)]
    (four_nonzero (F := F)) completed (by decide) (by decide)
  simpa only [{role}Output,{role}Left,{role}Right,mul_comm] using calculated
'''
    aliases = {
        'signLeft': 'negative', 'signRight': 'scaleLinear (-2) unsignedX',
        'xxLeft': 'signedX', 'xxRight': 'blindedX', 'yyLeft': 'signedY', 'yyRight': 'blindedY',
        'xyLeft': 'xxOutput', 'xyRight': 'yyOutput',
        'denominatorLeft': 'plus', 'denominatorRight': 'minus',
        'crossXLeft': 'signedX', 'crossXRight': 'blindedY', 'crossYLeft': 'signedY', 'crossYRight': 'blindedX',
        'xMinusLeft': 'crossXOutput ++ crossYOutput', 'xMinusRight': 'minus',
        'xOutputLeft': 'xMinusOutput', 'xOutputRight': 'inverse',
        'yPlusLeft': 'yyOutput ++ xxOutput', 'yPlusRight': 'plus',
        'yOutputLeft': 'yPlusOutput', 'yOutputRight': 'inverse',
        'inverseProductLeft': 'inverse', 'inverseProductRight': 'denominatorOutput',
        'signedX': 'unsignedX ++ signOutput', 'signedY': 'unsignedY',
        'plus': '[(0,1)] ++ scaleLinear d xyOutput',
        'minus': 'Compiler.subtract [(0,1)] (scaleLinear d xyOutput)'}
    for label, expression in aliases.items():
        source += f'''private theorem {label}_alias {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F) :
    eval rho {label} = eval rho ({expression}) := Compiler.canonical_equal rho _ _ (by decide)
'''
    for tag, rows in (('pre', 'preRows'), ('full', 'expectedRows')):
        source += f'''private theorem signed_{tag} {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (completed : Satisfies rho {rows}) (sign : Bool)
    (signValue : eval rho negative = if sign then 1 else 0) :
    signedPoint rho = GroupSignedPoint.signed sign (unsignedPoint rho) := by
  have product := sign_{tag} rho completed
  rw [signLeft_alias,signRight_alias,eval_scale,signValue] at product
  apply congrArg₂ Group.Point.mk
  · change eval rho signedX = _
    rw [signedX_alias,eval_append,product]
    simp only [GroupSignedPoint.signed,unsignedPoint,Int.cast_neg,Int.cast_ofNat]
    ring
  · change eval rho signedY = eval rho unsignedY
    exact signedY_alias rho
private theorem delta_{tag} {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (completed : Satisfies rho {rows}) :
    (d : F)*eval rho xyOutput = Group.delta (d : F) (signedPoint rho) (blindedPoint rho) := by
  have xx := xx_{tag} rho completed
  have yy := yy_{tag} rho completed
  have xy := xy_{tag} rho completed
  rw [xxLeft_alias,xxRight_alias] at xx
  rw [yyLeft_alias,yyRight_alias] at yy
  rw [xyLeft_alias,xyRight_alias,xx,yy] at xy
  rw [xy]
  simp only [Group.delta,signedPoint,blindedPoint]
  ring
private theorem plus_{tag} {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (completed : Satisfies rho {rows}) :
    eval rho plus = 1 + Group.delta (d : F) (signedPoint rho) (blindedPoint rho) := by
  rw [plus_alias,eval_append,eval_scale,delta_{tag} rho completed]
  simp only [eval,Int.cast_one,one_mul,add_zero,one]
private theorem minus_{tag} {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (completed : Satisfies rho {rows}) :
    eval rho minus = 1 - Group.delta (d : F) (signedPoint rho) (blindedPoint rho) := by
  rw [minus_alias,Compiler.eval_subtract,eval_scale,delta_{tag} rho completed]
  simp only [eval,Int.cast_one,one_mul,add_zero,one]
private theorem denominator_{tag} {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (completed : Satisfies rho {rows}) :
    eval rho denominatorOutput =
      (1 + Group.delta (d : F) (signedPoint rho) (blindedPoint rho))*
      (1 - Group.delta (d : F) (signedPoint rho) (blindedPoint rho)) := by
  rw [denominator_{tag if tag != 'pre' else 'pre'}]
  rw [denominatorLeft_alias,denominatorRight_alias,plus_{tag} rho one completed,minus_{tag} rho one completed]
'''
    # The product proof and algebraic denominator proof need distinct names.
    source = source.replace('private theorem denominator_pre {', 'private theorem denominator_product_pre {', 1)
    source = source.replace('private theorem denominator_full {', 'private theorem denominator_product_full {', 1)
    source = source.replace('  rw [denominator_pre]\n', '  rw [denominator_product_pre rho completed]\n')
    source = source.replace('  rw [denominator_full]\n', '  rw [denominator_product_full rho completed]\n')
    source += f'''theorem pre_signed {{F : Type}} [Field F] [CharP F modulus]
    (base : Nat → F) (sign : Bool) (signValue : eval base negative = if sign then 1 else 0) :
    signedPoint (preAssignment base) = GroupSignedPoint.signed sign (unsignedPoint base) := by
  have derived := signed_pre (preAssignment base) (pre_rows base) sign
    (by rw [pre_preserves base negative (by decide)]; exact signValue)
  have preserved : unsignedPoint (preAssignment base) = unsignedPoint base :=
    congrArg₂ Group.Point.mk (pre_preserves base unsignedX (by decide)) (pre_preserves base unsignedY (by decide))
  exact derived.trans (congrArg (GroupSignedPoint.signed sign) preserved)
theorem denominator_nonzero {{F : Type}} [Field F] [CharP F modulus]
    (base : Nat → F) (one : base 0 = 1) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (d : F)) (imaginarySquare : imaginary*imaginary = -1)
    (sign : Bool) (signValue : eval base negative = if sign then 1 else 0)
    (unsignedCurved : Group.OnCurve (d : F) (unsignedPoint base))
    (blindingCurved : Group.OnCurve (d : F) (blindedPoint base)) :
    eval (preAssignment base) {linear(reciprocal['denominator'])} ≠ 0 := by
  have preOne : preAssignment base 0 = 1 :=
    (GroupCircuitCompletion.run_preserves base preSteps kept [] pre_ordered 0 (by decide)).trans one
  have denominator := denominator_pre (preAssignment base) preOne (pre_rows base)
  have blinded : blindedPoint (preAssignment base) = blindedPoint base :=
    congrArg₂ Group.Point.mk (pre_preserves base blindedX (by decide)) (pre_preserves base blindedY (by decide))
  rw [pre_signed base sign signValue,blinded] at denominator
  have curved := GroupSignedPoint.signed_on_curve (d : F) sign (unsignedPoint base) unsignedCurved
  have legal := Group.denominators_nonzero (d : F) imaginary nonSquare imaginarySquare _ _ curved blindingCurved
  change eval (preAssignment base) denominatorOutput ≠ 0
  rw [denominator]
  exact mul_ne_zero legal.1 legal.2
theorem legal_steps {{F : Type}} [Field F] [CharP F modulus]
    (base : Nat → F) (one : base 0 = 1) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (d : F)) (imaginarySquare : imaginary*imaginary = -1)
    (sign : Bool) (signValue : eval base negative = if sign then 1 else 0)
    (unsignedCurved : Group.OnCurve (d : F) (unsignedPoint base))
    (blindingCurved : Group.OnCurve (d : F) (blindedPoint base)) : GroupCircuitCompletion.Legal base steps := by
  simp only [steps,preSteps,postSteps,inverseStep,List.append,List.cons_append,List.nil_append,
    GroupCircuitCompletion.Legal,GroupCircuitCompletion.Step.Legal,CompilerCompletion.Step.Legal,
    true_and,and_true,eval]
  change eval (preAssignment base) {linear(reciprocal['denominator'])} ≠ 0
  exact denominator_nonzero base one imaginary nonSquare imaginarySquare sign signValue unsignedCurved blindingCurved
theorem expected_rows_complete {{F : Type}} [Field F] [CharP F modulus]
    (base : Nat → F) (one : base 0 = 1) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (d : F)) (imaginarySquare : imaginary*imaginary = -1)
    (sign : Bool) (signValue : eval base negative = if sign then 1 else 0)
    (unsignedCurved : Group.OnCurve (d : F) (unsignedPoint base))
    (blindingCurved : Group.OnCurve (d : F) (blindedPoint base)) :
    Satisfies (completeAssignment base) expectedRows :=
  GroupCircuitCompletion.run_constructs base steps kept ordered
    (legal_steps base one imaginary nonSquare imaginarySquare sign signValue unsignedCurved blindingCurved)
'''
    source += '''private theorem endpoint {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (completed : Satisfies rho expectedRows) :
    outputPoint rho = Group.affineAdd (d : F) (signedPoint rho) (blindedPoint rho) := by
  have denominator := denominator_full rho one completed
  have inverseProduct := inverseProduct_full rho completed
  rw [inverseProductLeft_alias,inverseProductRight_alias] at inverseProduct
  have assertion := Compiler.checked_assertion_sound rho expectedRows inverseProductOutput [(0,1)] completed (by decide)
  have unit : eval rho [(0,1)] = 1 := by simp only [eval,Int.cast_one,one_mul,add_zero,one]
  have inverseRow : ((1+Group.delta (d : F) (signedPoint rho) (blindedPoint rho))*
      (1-Group.delta (d : F) (signedPoint rho) (blindedPoint rho)))*eval rho inverse = 1 := by
    rw [← denominator,mul_comm,← inverseProduct,assertion,unit]
  have xMinus := xMinus_full rho completed
  have xOutput := xOutput_full rho completed
  have crossX := crossX_full rho completed
  have crossY := crossY_full rho completed
  have yy := yy_full rho completed
  have xx := xx_full rho completed
  have yPlus := yPlus_full rho completed
  have yOutput := yOutput_full rho completed
  have xValue : (outputPoint rho).x = Group.cross (signedPoint rho) (blindedPoint rho)*
      (1-Group.delta (d : F) (signedPoint rho) (blindedPoint rho))*eval rho inverse := by
    change eval rho xOutputOutput = _
    simp only [xOutput,xOutputLeft_alias,xOutputRight_alias,xMinus,xMinusLeft_alias,xMinusRight_alias,
      eval_append,crossX,crossXLeft_alias,crossXRight_alias,crossY,crossYLeft_alias,crossYRight_alias,
      minus_full rho one completed]
    simp only [signedPoint,blindedPoint,Group.cross]
    ring
  have yValue : (outputPoint rho).y = Group.diagonal (signedPoint rho) (blindedPoint rho)*
      (1+Group.delta (d : F) (signedPoint rho) (blindedPoint rho))*eval rho inverse := by
    change eval rho yOutputOutput = _
    simp only [yOutput,yOutputLeft_alias,yOutputRight_alias,yPlus,yPlusLeft_alias,yPlusRight_alias,
      eval_append,yy,yyLeft_alias,yyRight_alias,xx,xxLeft_alias,xxRight_alias,plus_full rho one completed]
    simp only [signedPoint,blindedPoint,Group.diagonal]
    ring
  exact TransferSubgroup.shared_inverse_affine (d : F) (eval rho inverse) _ _ _ inverseRow xValue yValue
theorem original_coverage : ∀ actual ∈ rawRows, ∃ expected ∈ expectedRows,
    (Compiler.canonical modulus (Compiler.unoutline 200692 actual.a) = Compiler.canonical modulus expected.a ∨
     Compiler.canonical modulus (Compiler.unoutline 200692 actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
    Compiler.canonical modulus (Compiler.unoutline 200692 actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  simp only [rawRows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ''' + ' | '.join('rfl' for _ in sorted(raw)) + '\n'
    for i in sorted(raw):
        source += f'''  · refine ⟨{expected[i]},?_,by decide,by decide⟩
    simp [expectedRows,steps,preSteps,inverseStep,postSteps,GroupCircuitCompletion.emitted,
      GroupCircuitCompletion.Step.rows,CompilerCompletion.Step.rows,ScalarCompletion.productRows,
      GroupRowCompletion.quotientRows,Compiler.subtract,scaleLinear]
'''
    source += '''theorem actual_rows_complete {F : Type} [Field F] [CharP F modulus]
    (base : Nat → F) (one : base 0 = 1) (linked : base 200692 = base 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare (d : F)) (imaginarySquare : imaginary*imaginary = -1)
    (sign : Bool) (signValue : eval base negative = if sign then 1 else 0)
    (unsignedCurved : Group.OnCurve (d : F) (unsignedPoint base))
    (blindingCurved : Group.OnCurve (d : F) (blindedPoint base)) :
    Satisfies (completeAssignment base) rawRows ∧ outputPoint (completeAssignment base) =
      Group.affineAdd (d : F) (GroupSignedPoint.signed sign (unsignedPoint base)) (blindedPoint base) := by
  have completed := expected_rows_complete base one imaginary nonSquare imaginarySquare sign signValue unsignedCurved blindingCurved
  have completeOne : completeAssignment base 0 = 1 := (outside base 0 (by decide)).trans one
  have completeLink : completeAssignment base 200692 = completeAssignment base 0 := by
    rw [outside base 200692 (by decide),outside base 0 (by decide),linked]
  have observed := endpoint (completeAssignment base) completeOne completed
  have signed := signed_full (completeAssignment base) completed sign
    (by rw [outside_eval base negative (by decide)]; exact signValue)
  have unsigned : unsignedPoint (completeAssignment base) = unsignedPoint base :=
    congrArg₂ Group.Point.mk (outside_eval base unsignedX (by decide)) (outside_eval base unsignedY (by decide))
  have blinded : blindedPoint (completeAssignment base) = blindedPoint base :=
    congrArg₂ Group.Point.mk (outside_eval base blindedX (by decide)) (outside_eval base blindedY (by decide))
  rw [signed,unsigned,blinded] at observed
  exact ⟨CompilerSignedCompletion.original_rows (completeAssignment base) expectedRows rawRows 200692
    completeLink completed original_coverage,observed⟩
'''
    exports = ('ordered', 'writes_exact', 'outside', 'outside_eval', 'preserves_earlier_rows', 'pre_rows',
               'pre_preserves', 'pre_signed', 'denominator_nonzero', 'legal_steps',
               'expected_rows_complete', 'original_coverage', 'actual_rows_complete')
    for export in exports:
        source += '#print axioms ' + export + '\n'
    return namespace, _signature_audits(source + f'end ShielddSecurity.{namespace}\n')
