"""Required shared native table/frame exports for the actual balance65 loop.

Only augments the neutral precompute after strict actual source/row acceptance.
The primitive native SDK point and its upstream reader/model laws are input
contracts. No desired table coordinates or row satisfaction are supplied.
"""
from . import transfer_relation as relation
from .generate_hash_round import linear,_signature_audits


def augment(module,checked,plan,d,a,n):
    name,source=module
    if any(value[0]!='source' for key in ('base','twice','triple') for value in checked['points'][key]):
        raise relation.RelationError('balance native table exact source coordinates required')
    coordinates={key:tuple(checked['derived'][value[1]] for value in checked['points'][key])
                 for key in ('base','twice','triple')}
    if any(len(terms)!=1 or terms[0][1]!=1 for pair in coordinates.values() for terms in pair):
        raise relation.RelationError('balance native table exact seeded/quotient singleton coordinates')
    groups=plan.get('point_groups',[])
    if [group.get('index') for group in groups]!=[0,1]:
        raise relation.RelationError('balance native table exact double/add source order')
    for key,group in zip(('twice','triple'),groups):
        stages=plan['stages'][group['material_end']:group['stage_end']]
        if (len(stages)!=2 or any(stage.get('kind')!='quotient' for stage in stages) or
                coordinates[key]!=tuple(((stage['quotient'],1),) for stage in stages)):
            raise relation.RelationError('balance native table actual quotient output/source coordinates')
    x,y=[terms[0][0] for terms in coordinates['base']]
    if x==y or {x,y}&{0,1,2,6,checked['metadata']['constant_copy']}:
        raise relation.RelationError('balance native table seeded coordinates alias protected source columns')
    c=d.removesuffix('Completion')+'Cones'
    material=d.removesuffix('Completion')+'Materializations'
    arguments='fq fr model upstream backend point base'
    built=f'(completed {arguments})';first=f'(first {arguments})'
    def point(key,rho=built):
        return '(⟨'+','.join('eval '+rho+' '+linear(terms) for terms in coordinates[key])+'⟩ : Group.Point F)'
    support=[term for key in ('base','twice') for terms in coordinates[key] for term in terms]
    inside='(by intro term member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; subst term; decide)'
    extra=f'''def allWrites : List Nat := [{x},{y}] ++
  {material}.steps.flatMap GroupCircuitCompletion.Step.writes ++ {d}.x.writes ++ {d}.y.writes ++ writes
theorem outside (column : Nat) (excluded : column ∉ allWrites) :
    completed {arguments} column = base column := by
  have noSeed : column ∉ [{x},{y}] := by
    intro member; apply excluded
    simp only [allWrites,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl member)))
  have noMaterial : ∀ stage ∈ {material}.steps, column ∉ stage.writes := by
    intro stage present written; apply excluded
    simp only [allWrites,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨stage,present,written⟩))))
  have noX : column ∉ {d}.x.writes := by
    intro member; apply excluded
    simp only [allWrites,List.mem_append]
    exact Or.inl (Or.inl (Or.inr member))
  have noY : column ∉ {d}.y.writes := by
    intro member; apply excluded
    simp only [allWrites,List.mem_append]
    exact Or.inl (Or.inr member)
  have noAddition : column ∉ writes := by
    intro member; apply excluded
    exact List.mem_append_right _ member
  change {a}.completed ({d}.completed ({n}.seeded {arguments})) column = base column
  rw [addition_preserves _ column noAddition]
  have doublePreserved := (GroupQuotientPairCompletion.pair_preserves {d}.x {d}.y
    ({material}.materialAssignment ({n}.seeded {arguments})) column noX noY).trans
      (GroupCircuitOrder.run_outside ({n}.seeded {arguments}) {material}.steps column noMaterial)
  exact doublePreserved.trans (ShielddPointCoordinateSeed.seed_preserves fq fr ({c}.coefficientD : F)
    model upstream backend point {x} {y} base column noSeed)
theorem native_table_coordinates (imaginary : F)
    (nonSquare : Group.NoUnitSquare ({c}.coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
    (one : base 0 = 1) (linked : base {checked['metadata']['constant_copy']} = base 0) :
    {point('base')} = model.coordinates (upstream.embed (upstream.promote point)) ∧
    {point('twice')} = model.coordinates (2 • upstream.embed (upstream.promote point)) ∧
    {point('triple')} = model.coordinates (3 • upstream.embed (upstream.promote point)) := by
  have inputs := native_inputs {arguments} imaginary nonSquare imaginarySquare one linked
  have built := native_precompute_complete {arguments} imaginary nonSquare imaginarySquare one linked
  have supports : ({linear(support)} : Linear).all (fun term => decide (term.1 ∉ writes)) = true := by decide
  have agrees (terms : Linear) (inside : ∀ term ∈ terms, term ∈ ({linear(support)} : Linear)) :
      eval {built} terms = eval {first} terms := by
    apply eval_agrees
    intro term present
    exact addition_preserves _ term.1 (of_decide_eq_true (List.all_eq_true.mp supports term (inside term present)))
  have baseMeaning := inputs.2
  have twiceMeaning := inputs.1
  change {point('base',first)} = _ at baseMeaning
  change {point('twice',first)} = _ at twiceMeaning
  refine ⟨?_,?_,?_⟩
  · rw [agrees {linear(coordinates['base'][0])} {inside},agrees {linear(coordinates['base'][1])} {inside}]
    exact baseMeaning
  · rw [agrees {linear(coordinates['twice'][0])} {inside},agrees {linear(coordinates['twice'][1])} {inside}]
    exact twiceMeaning
  · simpa only [{a}.outputPoint,GroupQuotientPairCompletion.point,{a}.x,{a}.y,
      eval,Int.cast_one,one_mul,add_zero] using built.2
#print axioms outside
#print axioms native_table_coordinates
'''
    ending=f'end ShielddSecurity.{name}\n'
    if not source.endswith(ending):raise relation.RelationError('balance native precompute namespace ending')
    return name,_signature_audits(source[:-len(ending)]+extra+ending)
