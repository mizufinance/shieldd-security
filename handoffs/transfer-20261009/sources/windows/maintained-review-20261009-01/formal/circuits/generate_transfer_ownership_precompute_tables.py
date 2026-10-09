"""Actual variable-table and bit preservation at the native precompute boundary.

The point is read through the globally owned SDK/coordinate seed. Row truth,
two/three-base values and curve invariants are conclusions of the existing
actual double/add constructors; no desired table or point fact is an input.
"""
from . import generate_transfer_ownership_precompute_native as native
from . import transfer_ownership_completion as completion
from .generate_hash_round import _signature_audits


def generate(checked,extracted,readonly_lcs=()):
    n,_=native.generate(checked,extracted,readonly_lcs)
    if checked['metadata'].get('schema')!='shieldd-transfer-ownership-v1' or checked['metadata']['window_start']!=0:
        raise completion.relation.RelationError('ownership table companion exact first owned chunk')
    cones=completion.owner.cone_certificates(checked,extracted,0,True)
    plan=completion.window_plan(checked,extracted,readonly_lcs=readonly_lcs)
    if len(plan['point_groups'])<2:
        raise completion.relation.RelationError('ownership actual two precompute groups')
    formula=next(cone for cone in cones['cones'] if cone['role']=='formula0')
    base=[cones['observations'][identity][1] for identity in formula['inputs']]
    observed=lambda value:checked['derived'][value[1]] if value[0]=='source' else completion.canonical([(0,value[1])])
    expected=[base]
    for group in plan['point_groups'][:2]:
        stages=plan['stages'][group['material_end']:group['stage_end']]
        if len(stages)!=2 or any('quotient' not in stage for stage in stages):
            raise completion.relation.RelationError('ownership actual precomputed affine quotient pair')
        expected.append([completion.canonical([(stage['quotient'],1)]) for stage in stages])
    if any([observed(value) for value in checked['points'][role]]!=values
           for role,values in zip(('base','twice','triple'),expected)):
        raise completion.relation.RelationError('ownership exact actual shared native table coordinate join')
    if len(base)!=2 or any(len(terms)!=1 or terms[0][1]!=1 for terms in base):
        raise completion.relation.RelationError('ownership table exact source singleton seed')
    x,y=[terms[0][0] for terms in base];copy=checked['metadata']['constant_copy']
    source_columns=sorted({0,copy,*(column for terms in readonly_lcs for column,_ in terms),
        *(column for handle in checked['bits'] for column,_ in checked['derived'][handle])})
    if {x,y}&set(source_columns):
        raise completion.relation.RelationError('ownership native coordinate seed source-role separation')
    stem=n.removesuffix('NativePrecompute');d=stem+'Point0Completion';a=stem+'Point1Completion'
    m=stem+'Point0Materializations';seed=stem+'Point0CompletionNativeSeed';p=stem+'Program'
    name=stem+'NativeTables'
    blocks=[source_columns[index:index+16] for index in range(0,len(source_columns),16)]
    condition=f'(column ∈ {m}.kept ∧ column ∉ {n}.writes ∧ column ∉ [{x},{y}])'
    protection=f'''def sourceBlocks : List (List Nat) := {blocks}
private theorem sourceBlocks_flat : sourceBlocks.flatten = sourceColumns := by rfl
'''
    for index,block in enumerate(blocks):
        protection+=f'''private theorem source_checked{index} :
    ({block} : List Nat).all (fun column => decide {condition}) = true := by decide
'''
    protection+=f'''private theorem source_facts (column : Nat) (member : column ∈ sourceColumns) :
    {condition} := by
  have flattened : column ∈ sourceBlocks.flatten := by
    rw [sourceBlocks_flat]
    exact member
  rcases List.mem_flatten.mp flattened with ⟨block,present,inside⟩
  simp only [sourceBlocks,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with '''+' | '.join('rfl' for _ in blocks)+'\n'
    for index in range(len(blocks)):
        protection+=f'  · exact of_decide_eq_true (List.all_eq_true.mp source_checked{index} column inside)\n'
    source=f'''import ShielddSecurity.{n}
import ShielddSecurity.{p}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
open GroupFixedCircuitCompletion
def sourceColumns : List Nat := {source_columns}
def tables : GroupVariableCircuitCompletion.Tables := {p}.tables
{protection}
private theorem triple_coordinates {{F : Type}} [Field F] (rho : Nat → F) :
    GroupFixedCircuitCompletion.point rho tables.triple = {a}.outputPoint rho := by
  simp only [tables,{p}.tables,GroupFixedCircuitCompletion.point,{a}.outputPoint,
    GroupQuotientPairCompletion.point,{a}.x,{a}.y,eval,Int.cast_one,one_mul,add_zero]
private theorem identity_coordinates {{F : Type}} [Field F] (rho : Nat → F) (one : rho 0 = 1) :
    GroupFixedCircuitCompletion.point rho ({p}.program false false).input = Group.identityPoint := by
  change (⟨eval rho [],eval rho [(0,1)]⟩ : Group.Point F) = Group.identityPoint
  simp only [eval,Int.cast_one,one_mul,add_zero,one,Group.identityPoint]
variable {{F : Type}} [Field F] [CharP F {d}.modulus]
variable {{E S R K Q Signing J : Type}} [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (model : Group.StandardCurveModel J ({stem}Point0Cones.coefficientD : F))
variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr ({stem}Point0Cones.coefficientD : F) model)
variable {{Encoded Native : Type}} (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
variable (point : S) (base : Nat → F)
theorem protected_columns (linked : base {copy} = base 0) :
    ∀ column ∈ sourceColumns, {n}.completed fq fr model upstream backend point base column = base column := by
  let seeded := {seed}.seeded fq fr model upstream backend point base
  have seedLink : seeded {copy} = seeded 0 := by
    dsimp only [seeded,{seed}.seeded]
    rw [ShielddPointCoordinateSeed.seed_preserves fq fr ({stem}Point0Cones.coefficientD : F)
      model upstream backend point {x} {y} base {copy} (by decide),
      ShielddPointCoordinateSeed.seed_preserves fq fr ({stem}Point0Cones.coefficientD : F)
      model upstream backend point {x} {y} base 0 (by decide),linked]
  intro column member
  have facts := source_facts column member
  exact ({n}.addition_preserves ({n}.first fq fr model upstream backend point base) column facts.2.1).trans
    (({d}.protected_columns seeded seedLink column facts.1).trans
      (ShielddPointCoordinateSeed.seed_preserves fq fr ({stem}Point0Cones.coefficientD : F)
        model upstream backend point {x} {y} base column facts.2.2))
theorem table_coordinates (imaginary : F)
    (nonSquare : Group.NoUnitSquare ({stem}Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) (one : base 0 = 1) (linked : base {copy} = base 0) :
    point ({n}.completed fq fr model upstream backend point base) tables.base =
      model.coordinates (upstream.embed (upstream.promote point)) ∧
    point ({n}.completed fq fr model upstream backend point base) tables.twice =
      model.coordinates (2 • upstream.embed (upstream.promote point)) ∧
    point ({n}.completed fq fr model upstream backend point base) tables.triple =
      model.coordinates (3 • upstream.embed (upstream.promote point)) := by
  let built := {n}.first fq fr model upstream backend point base
  have inputs := {n}.native_inputs fq fr model upstream backend point base imaginary nonSquare imaginarySquare one linked
  have full := {n}.native_precompute_complete fq fr model upstream backend point base imaginary nonSquare imaginarySquare one linked
  have checked : (tables.base.1 ++ tables.base.2 ++ tables.twice.1 ++ tables.twice.2).all
      (fun term => decide (term.1 ∉ {n}.writes)) = true := by decide
  have preserved (terms : Linear) (inside : ∀ term ∈ terms,
      term ∈ tables.base.1 ++ tables.base.2 ++ tables.twice.1 ++ tables.twice.2) :
      eval ({n}.completed fq fr model upstream backend point base) terms = eval built terms := by
    apply eval_agrees
    intro term member
    exact {n}.addition_preserves built term.1
      (of_decide_eq_true (List.all_eq_true.mp checked term (inside term member)))
  have keepBase : point ({n}.completed fq fr model upstream backend point base) tables.base = point built tables.base := by
    exact congrArg₂ Group.Point.mk (preserved _ (by intro term member; simp [member]))
      (preserved _ (by intro term member; simp [member]))
  have keepTwice : point ({n}.completed fq fr model upstream backend point base) tables.twice = point built tables.twice := by
    exact congrArg₂ Group.Point.mk (preserved _ (by intro term member; simp [member]))
      (preserved _ (by intro term member; simp [member]))
  have baseJoin : point built tables.base = {a}.rightPoint built := by rfl
  have twiceJoin : point built tables.twice = {a}.inputPoint built := by rfl
  have tripleJoin : point ({n}.completed fq fr model upstream backend point base) tables.triple =
      {a}.outputPoint ({n}.completed fq fr model upstream backend point base) :=
    triple_coordinates _
  exact ⟨keepBase.trans (baseJoin.trans inputs.2),keepTwice.trans (twiceJoin.trans inputs.1),tripleJoin.trans full.2⟩
theorem table_curves (imaginary : F)
    (nonSquare : Group.NoUnitSquare ({stem}Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) (one : base 0 = 1) (linked : base {copy} = base 0) :
    GroupVariableCircuitCompletion.Curved ({stem}Point0Cones.coefficientD : F) tables
      ({n}.completed fq fr model upstream backend point base) := by
  have coordinates := table_coordinates fq fr model upstream backend point base imaginary nonSquare imaginarySquare one linked
  unfold GroupVariableCircuitCompletion.Curved
  rw [coordinates.1,coordinates.2.1,coordinates.2.2]
  exact ⟨model.onCurve _,model.onCurve _,model.onCurve _⟩
theorem identity_input (linked : base {copy} = base 0) (one : base 0 = 1) :
    Group.OnCurve ({stem}Point0Cones.coefficientD : F)
      (point ({n}.completed fq fr model upstream backend point base) ({p}.program false false).input) := by
  have oneBuilt : {n}.completed fq fr model upstream backend point base 0 = 1 :=
    (protected_columns fq fr model upstream backend point base linked 0 (by decide)).trans one
  have same := identity_coordinates ({n}.completed fq fr model upstream backend point base) oneBuilt
  rw [same,← model.identity]
  exact model.onCurve 0
theorem prior_rows_complete (imaginary : F)
    (nonSquare : Group.NoUnitSquare ({stem}Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) (one : base 0 = 1) (linked : base {copy} = base 0) :
    Satisfies ({n}.completed fq fr model upstream backend point base) {p}.priorRows :=
  ({n}.native_precompute_complete fq fr model upstream backend point base imaginary nonSquare imaginarySquare one linked).1
'''
    # The native argument is named point; qualify the circuit-coordinate
    # constructor so an ordinary argument cannot shadow it.
    source=source.replace('    point (','    GroupFixedCircuitCompletion.point (').replace(' : point (',' : GroupFixedCircuitCompletion.point (').replace(' = point built',' = GroupFixedCircuitCompletion.point built').replace('      (point (','      (GroupFixedCircuitCompletion.point (').replace('      have same : point (','      have same : GroupFixedCircuitCompletion.point (')
    source=source.replace('have baseJoin : point built','have baseJoin : GroupFixedCircuitCompletion.point built').replace('have twiceJoin : point built','have twiceJoin : GroupFixedCircuitCompletion.point built').replace('have same : point (','have same : GroupFixedCircuitCompletion.point (')
    for export in ('protected_columns','table_coordinates','table_curves','identity_input','prior_rows_complete'):
        source+='#print axioms '+export+'\n'
    return name,_signature_audits(source+f'end ShielddSecurity.{name}\n')
