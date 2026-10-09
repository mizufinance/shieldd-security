"""Derive the actual folded first-window selector/output and curve closure."""
from . import transfer_ownership_completion as completion
from . import generate_transfer_ownership_folded_window_completion as folded
from .generate_transfer_ownership_completion import lower_stage
from .generate_hash_round import linear, _signature_audits


def generate(checked, extracted, readonly_lcs=()):
    local, _ = folded.generate(checked, extracted, readonly_lcs)
    plan = completion.window_plan(checked, extracted, 0, False, readonly_lcs)
    cones = completion.owner.cone_certificates(checked, extracted, 0, False)
    bits=tuple(checked['derived'][handle] for handle in checked['bits'][250:252])
    return render_folded_curve(checked,plan,cones,local,bits)


def render_folded_curve(checked,plan,cones,local,bits,*,native_inputs=False):
    """Neutral first-identity curve/output constructor; exact native bit cut."""
    if plan.get('window_index',0)!=0 or len(bits)!=2:
        raise completion.relation.RelationError('folded curve first window/bit pair')
    selected = [next(cone for cone in cones['cones'] if cone['role'] == 'formula'+str(i)) for i in (20,21)]
    observe = lambda value: checked['derived'][value[1]] if value[0] == 'source' else completion.canonical([(0,value[1])])
    points = {role: tuple(map(observe, checked['points'][role])) for role in ('base','twice','triple')}
    low, high = bits
    inputs = [*points['base'], *points['twice'], *points['triple'], low, high]
    expected_inputs=inputs
    if native_inputs:
        observed=[*checked['points']['base'],*checked['points']['twice'],*checked['points']['triple'],
                  *checked['window_bits'][0]]
        expected_inputs=[terms for role,terms in zip(observed,inputs) if role[0]=='source']
    if any([cones['observations'][identity][1] for identity in cone['inputs']] != expected_inputs for cone in selected):
        raise completion.relation.RelationError('ownership folded selector exact eight shared source roles')
    group = plan['point_groups'][2]
    stages = plan['stages'][group['material_end']:group['stage_end']]
    selector = tuple(map(observe, checked['windows'][0][3]))
    result = tuple(map(observe, checked['windows'][0][4]))
    if any(stage['input'] != selector[axis] or stage['remainder'] != () or
           result[axis] != ((stage['output'],1),) or
           cones['observations'][selected[axis]['output']][1] != selector[axis]
           for axis,stage in enumerate(stages)):
        raise completion.relation.RelationError('ownership folded selector/output exact linear coordinate endpoints')
    stem = local.removesuffix('FoldedCompletion');c=stem+'Point4Cones';m=stem+'Point4Materializations'
    name = stem+'FoldedCurveCompletion';copy=checked['metadata']['constant_copy']
    roles = ('baseX','baseY','twiceX','twiceY','tripleX','tripleY','low','high')
    source=f'''import ShielddSecurity.{local}
import ShielddSecurity.{m}
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
'''
    for role,terms in zip(roles,inputs):source+=f'def {role} : Linear := {linear(terms)}\n'
    for role in ('base','twice','triple'):
        source+=f'''def {role}Point {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F :=
  ⟨eval rho {role}X,eval rho {role}Y⟩
'''
    source+=f'''def selected {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F :=
  ⟨eval rho {linear(selector[0])},eval rho {linear(selector[1])}⟩
def output {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F :=
  ⟨rho {stages[0]['output']},rho {stages[1]['output']}⟩
def linearSteps : List GroupCircuitCompletion.Step := [{','.join(lower_stage(stage)[0] for stage in stages)}]
private theorem eval_kept {{F : Type}} [Field F] [CharP F {local}.modulus]
    (base : Nat → F) (linked : base {copy} = base 0) (terms : Linear)
    (inside : ∀ term ∈ terms, term.1 ∈ {m}.kept) :
    eval ({m}.materialAssignment base) terms = eval base terms := by
  apply eval_agrees; intro term member
  exact ({m}.material_rows_complete base linked).2 term.1 (inside term member)
theorem material_selected {{F : Type}} [Field F] [CharP F {local}.modulus]
    (base : Nat → F) (one : base 0 = 1) (linked : base {copy} = base 0) :
    selected ({m}.materialAssignment base) = Group.windowPoint (eval base low) (eval base high)
      (basePoint base) (twicePoint base) (triplePoint base) := by
  apply congrArg₂ Group.Point.mk
'''
    for axis,cone in enumerate(selected):
        role=cone['role'];output=c+'.'+role+'_'+cone['output']
        source+=f'''  · have value := {m}.{role}_constructed base one linked
    have identified : eval ({m}.materialAssignment base) {linear(selector[axis])} =
        eval ({m}.materialAssignment base) {output} := Compiler.canonical_equal _ _ _ (by decide)
    change eval ({m}.materialAssignment base) {linear(selector[axis])} = _
    rw [identified,value]
'''
        preserved_inputs = [f'eval_kept base linked {c}.{role}_{identity} (by decide)'
                            for identity in cone['inputs']]
        source += '    simp only ['+','.join(preserved_inputs)+']\n'
        declarations=','.join(c+'.'+role+'_'+identity for identity in cone['inputs'])
        source+=f'''    simp only [{declarations},basePoint,twicePoint,triplePoint,{','.join(roles)},
      Group.windowPoint,Group.chooseCoordinate{',eval' if native_inputs else ''}]
    ring
'''
    source+=f'''theorem assignment_factor {{F : Type}} [Field F] (base : Nat → F) :
    {local}.completeAssignment base = GroupCircuitCompletion.run ({m}.materialAssignment base) linearSteps := by
  simp only [{local}.completeAssignment,{local}.completionSteps,{m}.materialAssignment,{m}.steps,linearSteps,
    GroupCircuitCompletion.run,GroupCircuitCompletion.Step.run,CompilerCompletion.Step.run]
theorem selected_output {{F : Type}} [Field F] [CharP F {local}.modulus]
    (base : Nat → F) : output ({local}.completeAssignment base) = selected ({m}.materialAssignment base) := by
  rw [assignment_factor]
  let rho := {m}.materialAssignment base
  have xValue : CompilerLinearCompletion.extend rho {linear(stages[0]['input'])} [] {stages[0]['output']} {stages[0]['output']} =
      eval rho {linear(selector[0])} := by simp [CompilerLinearCompletion.extend,patchAssignment,eval]
  have yInput : eval (CompilerLinearCompletion.extend rho {linear(stages[0]['input'])} [] {stages[0]['output']})
      {linear(stages[1]['input'])} = eval rho {linear(selector[1])} := by
    apply eval_agrees; intro term member
    exact CompilerLinearCompletion.preserves rho {linear(stages[0]['input'])} [] {stages[0]['output']} term.1
      (by have checked : {linear(stages[1]['input'])}.all (fun term => decide (term.1 ≠ {stages[0]['output']})) = true := by decide
          exact of_decide_eq_true (List.all_eq_true.mp checked term member))
  have yValue : CompilerLinearCompletion.extend
      (CompilerLinearCompletion.extend rho {linear(stages[0]['input'])} [] {stages[0]['output']})
      {linear(stages[1]['input'])} [] {stages[1]['output']} {stages[1]['output']} = eval rho {linear(selector[1])} := by
    change (eval (CompilerLinearCompletion.extend rho {linear(stages[0]['input'])} [] {stages[0]['output']})
      {linear(stages[1]['input'])} - 0) = eval rho {linear(selector[1])}
    simpa only [sub_zero] using yInput
  change Group.Point.mk
    (CompilerLinearCompletion.extend (CompilerLinearCompletion.extend rho {linear(stages[0]['input'])} [] {stages[0]['output']})
      {linear(stages[1]['input'])} [] {stages[1]['output']} {stages[0]['output']})
    (CompilerLinearCompletion.extend (CompilerLinearCompletion.extend rho {linear(stages[0]['input'])} [] {stages[0]['output']})
      {linear(stages[1]['input'])} [] {stages[1]['output']} {stages[1]['output']}) = _
  exact congrArg₂ Group.Point.mk
    ((CompilerLinearCompletion.preserves _ _ _ {stages[1]['output']} {stages[0]['output']} (by decide)).trans xValue) yValue
theorem actual_window_complete {{F : Type}} [Field F] [CharP F {local}.modulus]
    (base : Nat → F) (one : base 0 = 1) (linked : base {copy} = base 0) (lowBit highBit : Bool)
    (lowValue : eval base low = if lowBit then 1 else 0) (highValue : eval base high = if highBit then 1 else 0)
    (baseValid : Group.OnCurve ({c}.coefficientD : F) (basePoint base))
    (twiceValid : Group.OnCurve ({c}.coefficientD : F) (twicePoint base))
    (tripleValid : Group.OnCurve ({c}.coefficientD : F) (triplePoint base)) :
    Satisfies ({local}.completeAssignment base) {local}.rawRows ∧
    Group.OnCurve ({c}.coefficientD : F) (output ({local}.completeAssignment base)) := by
  refine ⟨({local}.constructs base linked).1,?_⟩
  rw [selected_output base,material_selected base one linked,lowValue,highValue]
  exact Group.window_onCurve ({c}.coefficientD : F) lowBit highBit
    (basePoint base) (twicePoint base) (triplePoint base) baseValid twiceValid tripleValid
#print axioms material_selected
#print axioms assignment_factor
#print axioms selected_output
#print axioms actual_window_complete
end ShielddSecurity.{name}
'''
    return name,_signature_audits(source)
