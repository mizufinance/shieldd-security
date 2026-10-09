"""Construct one actual later double/double/select/add window on one assignment.

Each quotient is supplied by a maintained curve-derived local constructor.
Finite actual write/support certificates retain the earlier constructed rows;
the selector is derived from its owned materializations. Whole-loop seeding,
native table interpretation, scalar bits and all126 windows remain mandatory.
"""
from . import transfer_ownership_completion as completion
from .generate_transfer_ownership_completion import lower_stage
from .generate_hash_round import linear, _signature_audits


def generate(checked, extracted, window_offset, readonly_lcs=()):
    if type(window_offset) is not int or not 0 <= window_offset < len(checked['windows']):
        raise completion.relation.RelationError('ownership typed bounded whole window selection')
    plan = completion.window_plan(checked, extracted, window_offset, False, readonly_lcs)
    prefix = 'RuntimeRnkWindow' if checked['metadata'].get('schema') == 'shieldd-transfer-rnk-dh-v1' else 'RuntimeOwnershipWindow'
    return render_window(checked,plan,window_offset,prefix)


def render_window(checked,plan,window_offset,prefix):
    """Neutral exact double/double/select/add constructor after strict ingress."""
    import re
    if re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',prefix) is None:
        raise completion.relation.RelationError('whole window namespace')
    if plan['window_index'] == 0 or len(plan['point_groups']) != 3:
        raise completion.relation.RelationError('ownership whole later window three nonfolded operations')
    groups = plan['point_groups']; first_index = 2+3*window_offset
    if [(group['index'],group['kind']) for group in groups] != [
            (first_index,'double'), (first_index+1,'double'), (first_index+2,'add')]:
        raise completion.relation.RelationError('ownership whole exact double/double/add ordering')
    observe = lambda value: checked['derived'][value[1]] if value[0] == 'source' else completion.canonical([(0,value[1])])
    window = checked['windows'][window_offset]
    points = [tuple(map(observe, pair)) for pair in window]
    for index, group in enumerate(groups):
        coordinates = plan['stages'][group['material_end']:group['stage_end']]
        if len(coordinates) != 2 or any(stage['kind'] != 'quotient' for stage in coordinates) or \
                tuple(((stage['quotient'],1),) for stage in coordinates) != points[(1,2,4)[index]]:
            raise completion.relation.RelationError('ownership whole exact nonlinear coordinate outputs')
    stem = prefix+f'{plan["window_index"]:03d}'
    names = [stem+f'Point{group["index"]}Completion' for group in groups]
    mats = [name.removesuffix('Completion')+'Materializations' for name in names]
    cones = [name.removesuffix('Completion')+'Cones' for name in names]
    d0,d1,add = names; m0,m1,ma = mats; c0,c1,ca = cones
    selector = stem+f'Point{groups[2]["index"]}SelectorCompletion'; name = stem+'CurveCompletion'
    copy = checked['metadata']['constant_copy']; modulus = completion.relation.MODULUS
    source = ''.join(f'import ShielddSecurity.{module}\n' for module in [*names,selector,'GroupCircuitSequenceCompletion','GroupFixedCircuitCompletion','TransferOwnership'])
    source += f'''set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
def modulus : Nat := {modulus}
def d : Int := {c0}.coefficientD
'''
    for label, group, material in zip(('firstSteps','secondSteps','addSteps'), groups, mats):
        suffix = ','.join(lower_stage(stage)[0] for stage in plan['stages'][group['material_end']:group['stage_end']])
        source += f'def {label} : List GroupCircuitCompletion.Step := {material}.steps ++ [{suffix}]\n'
    source += f'''def steps : List GroupCircuitCompletion.Step := firstSteps ++ secondSteps ++ addSteps
def kept : List Nat := {plan['protected']}
def firstRows : List Row := {c0}.rawRows ++ {d0}.quotientRaw
def secondRows : List Row := {c1}.rawRows ++ {d1}.quotientRaw
def addRows : List Row := {ca}.rawRows ++ {add}.quotientRaw
def rawRows : List Row := (firstRows ++ secondRows) ++ addRows
def afterFirst {{F : Type}} [Field F] (base : Nat → F) : Nat → F := {d0}.completed base
def beforeAdd {{F : Type}} [Field F] (base : Nat → F) : Nat → F := {d1}.completed (afterFirst base)
def completeAssignment {{F : Type}} [Field F] (base : Nat → F) : Nat → F := {add}.completed (beforeAdd base)
private theorem first_factor {{F : Type}} [Field F] (base : Nat → F) :
    GroupCircuitCompletion.run base firstSteps = afterFirst base := by
  rw [firstSteps,GroupCircuitSequenceCompletion.run_append]
  rfl
private theorem second_factor {{F : Type}} [Field F] (base : Nat → F) :
    GroupCircuitCompletion.run base secondSteps = {d1}.completed base := by
  rw [secondSteps,GroupCircuitSequenceCompletion.run_append]
  rfl
private theorem add_factor {{F : Type}} [Field F] (base : Nat → F) :
    GroupCircuitCompletion.run base addSteps = {add}.completed base := by
  rw [addSteps,GroupCircuitSequenceCompletion.run_append]
  rfl
theorem completion_factor {{F : Type}} [Field F] (base : Nat → F) :
    GroupCircuitCompletion.run base steps = completeAssignment base := by
  rw [steps,GroupCircuitSequenceCompletion.run_append,GroupCircuitSequenceCompletion.run_append,
    first_factor,second_factor,add_factor]
  rfl
private theorem second_fresh : ∀ row ∈ firstRows, ∀ term ∈ row.a ++ row.b,
    term.1 ∉ GroupCircuitSequenceCompletion.writes secondSteps := by
  have checked : firstRows.all (fun row => (row.a ++ row.b).all
      (fun term => decide (term.1 ∉ GroupCircuitSequenceCompletion.writes secondSteps))) = true := by decide
  intro row member term present
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked row member) term present)
private theorem add_fresh : ∀ row ∈ firstRows ++ secondRows, ∀ term ∈ row.a ++ row.b,
    term.1 ∉ GroupCircuitSequenceCompletion.writes addSteps := by
  have checked : (firstRows ++ secondRows).all (fun row => (row.a ++ row.b).all
      (fun term => decide (term.1 ∉ GroupCircuitSequenceCompletion.writes addSteps))) = true := by decide
  intro row member term present
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked row member) term present)
theorem protected_columns {{F : Type}} [Field F] (base : Nat → F) (column : Nat)
    (member : column ∈ kept) : completeAssignment base column = base column := by
  rw [← completion_factor]
  have checked : kept.all (fun column => decide (column ∉ GroupCircuitSequenceCompletion.writes steps)) = true := by decide
  exact GroupCircuitSequenceCompletion.run_preserves base steps column
    (of_decide_eq_true (List.all_eq_true.mp checked column member))
private theorem eval_before_add {{F : Type}} [Field F] [CharP F modulus]
    (base : Nat → F) (linked : base {copy} = base 0) (terms : Linear)
    (insideFirst : ∀ term ∈ terms, term.1 ∈ {m0}.kept)
    (insideSecond : ∀ term ∈ terms, term.1 ∈ {m1}.kept) :
    eval (beforeAdd base) terms = eval base terms := by
  have firstLink : afterFirst base {copy} = afterFirst base 0 := by
    change {d0}.completed base {copy} = {d0}.completed base 0
    rw [{d0}.protected_columns base linked {copy} (by decide),
      {d0}.protected_columns base linked 0 (by decide),linked]
  apply eval_agrees
  intro term member
  exact ({d1}.protected_columns (afterFirst base) firstLink term.1 (insideSecond term member)).trans
    ({d0}.protected_columns base linked term.1 (insideFirst term member))
private theorem second_input {{F : Type}} [Field F] (base : Nat → F) :
    {d1}.inputPoint base = {d0}.outputPoint base := by
  simp only [{d1}.inputPoint,{d1}.inputX,{d1}.inputY,{d0}.outputPoint,
    GroupQuotientPairCompletion.point,{d0}.x,{d0}.y,eval,Int.cast_one,one_mul,add_zero]
private theorem add_input {{F : Type}} [Field F] (base : Nat → F) :
    {add}.inputPoint base = {d1}.outputPoint base := by
  simp only [{add}.inputPoint,{add}.inputX,{add}.inputY,{d1}.outputPoint,
    GroupQuotientPairCompletion.point,{d1}.x,{d1}.y,eval,Int.cast_one,one_mul,add_zero]
private theorem selected_input {{F : Type}} [Field F] (base : Nat → F) :
    {add}.rightPoint base = {selector}.selected base := rfl
'''
    source += f'''theorem actual_window_complete {{F : Type}} [Field F] [CharP F modulus]
    (base : Nat → F) (one : base 0 = 1) (linked : base {copy} = base 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare (d : F)) (imaginarySquare : imaginary*imaginary = -1)
    (lowBit highBit : Bool)
    (incoming : Group.OnCurve (d : F) ({d0}.inputPoint base))
    (lowValue : eval base {selector}.low = if lowBit then 1 else 0)
    (highValue : eval base {selector}.high = if highBit then 1 else 0)
    (baseValid : Group.OnCurve (d : F) ({selector}.basePoint base))
    (twiceValid : Group.OnCurve (d : F) ({selector}.twicePoint base))
    (tripleValid : Group.OnCurve (d : F) ({selector}.triplePoint base)) :
    Satisfies (completeAssignment base) rawRows ∧
      Group.OnCurve (d : F) ({add}.outputPoint (completeAssignment base)) := by
  have first := {d0}.actual_point_complete imaginary nonSquare imaginarySquare base one linked incoming
  have firstOne : afterFirst base 0 = 1 := ({d0}.protected_columns base linked 0 (by decide)).trans one
  have firstLink : afterFirst base {copy} = afterFirst base 0 := by
    change {d0}.completed base {copy} = {d0}.completed base 0
    rw [{d0}.protected_columns base linked {copy} (by decide),{d0}.protected_columns base linked 0 (by decide),linked]
  have secondIncoming : Group.OnCurve ({c1}.coefficientD : F) ({d1}.inputPoint (afterFirst base)) := by
    rw [second_input]
    exact first.2.2
  have second := {d1}.actual_point_complete imaginary nonSquare imaginarySquare (afterFirst base) firstOne firstLink secondIncoming
  have nextOne : beforeAdd base 0 = 1 := ({d1}.protected_columns (afterFirst base) firstLink 0 (by decide)).trans firstOne
  have nextLink : beforeAdd base {copy} = beforeAdd base 0 := by
    change {d1}.completed (afterFirst base) {copy} = {d1}.completed (afterFirst base) 0
    rw [{d1}.protected_columns (afterFirst base) firstLink {copy} (by decide),
      {d1}.protected_columns (afterFirst base) firstLink 0 (by decide),firstLink]
'''
    for label in ('base','twice','triple'):
        source += f'''  have {label}Preserved : {selector}.{label}Point (beforeAdd base) = {selector}.{label}Point base := by
    exact congrArg₂ Group.Point.mk
      (eval_before_add base linked {selector}.{label}X (by decide) (by decide))
      (eval_before_add base linked {selector}.{label}Y (by decide) (by decide))
'''
    source += f'''  have selectedValid := {selector}.material_curve (beforeAdd base) nextOne nextLink lowBit highBit
    ((eval_before_add base linked {selector}.low (by decide) (by decide)).trans lowValue)
    ((eval_before_add base linked {selector}.high (by decide) (by decide)).trans highValue)
    (by rw [basePreserved]; exact baseValid)
    (by rw [twicePreserved]; exact twiceValid)
    (by rw [triplePreserved]; exact tripleValid)
  have addIncoming : Group.OnCurve ({ca}.coefficientD : F) ({add}.inputPoint (beforeAdd base)) := by
    rw [add_input]
    exact second.2.2
  have added := {add}.actual_point_complete imaginary nonSquare imaginarySquare (beforeAdd base) nextOne nextLink
    addIncoming (by rw [selected_input]; exact selectedValid)
  have earlierSecond : Satisfies (beforeAdd base) firstRows := by
    change Satisfies ({d1}.completed (afterFirst base)) firstRows
    rw [← second_factor]
    exact GroupCircuitSequenceCompletion.preserves_rows (afterFirst base) secondSteps firstRows first.1 second_fresh
  have earlier : Satisfies (beforeAdd base) (firstRows ++ secondRows) := by
    intro row member
    rcases List.mem_append.mp member with before | now
    · exact earlierSecond row before
    · exact second.1 row now
  have retained : Satisfies (completeAssignment base) (firstRows ++ secondRows) := by
    change Satisfies ({add}.completed (beforeAdd base)) _
    rw [← add_factor]
    exact GroupCircuitSequenceCompletion.preserves_rows (beforeAdd base) addSteps _ earlier add_fresh
  constructor
  · intro row member
    change row ∈ (firstRows ++ secondRows) ++ addRows at member
    rcases List.mem_append.mp member with before | now
    · exact retained row before
    · exact added.1 row now
  · exact added.2.2
#print axioms completion_factor
#print axioms protected_columns
#print axioms actual_window_complete
end ShielddSecurity.{name}
'''
    return name, _signature_audits(source)
