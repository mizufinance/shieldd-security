"""Native first denominator/cubic constructor on exact owned map rows."""
from . import transfer_asset_map as maps,transfer_asset_map_completion as completion
from . import transfer_arithmetic as arithmetic,transfer_relation as relation
from .transfer_balance_rows import canonical,combine


def plan(data,extracted,accepted_roles):
    recipe=completion.plan(data,extracted,accepted_roles);checked=recipe['checked'];v=checked['values']
    rows=recipe['normalized'];by_rows={tuple(step['rows']):step for step in recipe['steps']}
    def product(label,left,right,output=None):
        matches=[(node,target) for node,a,b,target in checked['nonlinear']
                 if ((a,b)==(left,right) or (b,a)==(left,right)) and (output is None or target==output)]
        if len(matches)!=1:raise relation.RelationError('first cubic unique actual product '+label)
        node,target=matches[0];certificate=arithmetic.product_certificate(left,right,target,rows)
        step=by_rows.get(tuple(certificate['rows']))
        if step is None:raise relation.RelationError('first cubic original materialized product '+label)
        return dict(label=label,node=node,left=left,right=right,target=target,certificate=certificate,step=step)
    tv=product('tv',maps._scale(v['u'],5),v['u'],v['tv'])
    first=product('first',combine(v['x1'],maps._constant(maps.C1)),v['x1'])
    cubic=product('cubic',combine(first['target'],maps._constant(maps.C2)),v['x1'],v['gx1'])
    quotient=maps.certificates(data,extracted,accepted_roles)['quotients'][0]
    inverse=by_rows.get(tuple(quotient['rows'][:2]))
    if inverse is None or inverse['kind']!='product':
        raise relation.RelationError('first cubic original quotient product construction')
    q=recipe['seeds']['firstInverse'];steps=[tv['step'],inverse,first['step'],cubic['step']]
    known={0,q,*[column for column,_ in v['u']]};owned={q};material=set()
    for step in steps:
        reads={column for lc in (([step['input']] if step['kind']=='square' else [step['left'],step['right']])+[step['remainder']]) for column,_ in lc}
        if not reads<=known or known.intersection(step['writes']):
            raise relation.RelationError('first cubic exact construction dependency/freshness')
        known.update(step['writes']);owned.update(step['writes']);material.update(step['rows'])
    copy=checked['metadata']['constant_copy']
    if owned.intersection({0,1,2,copy,*[column for column,_ in v['u']]}):
        raise relation.RelationError('first cubic writes overlap actual input/public/committed/copy support')
    delta=combine(quotient['output'],maps.ONE,-1)
    matches=[i for i,row in rows.items() if row in ((delta,()),(maps._scale(delta,-1),()))]
    if len(matches)!=1:raise relation.RelationError('first cubic exact first inverse assertion')
    indices=sorted(material|{matches[0],recipe['link_row']})
    inverse_product=dict(label='inverseProduct',left=quotient['quotient'],
                         right=quotient['denominator'],target=quotient['output'],certificate=quotient)
    return dict(recipe=recipe,values=v,products=[tv,first,cubic,inverse_product],quotient=quotient,
                q=q,steps=steps,owned=sorted(owned),indices=indices,
                raw={i:recipe['raw'][i] for i in indices})


def construct(data,extracted,accepted_roles,base):
    result=plan(data,extracted,accepted_roles);rho=dict(base);p=maps.P
    copy=result['recipe']['checked']['metadata']['constant_copy']
    if rho.get(0)!=1 or rho.get(copy)!=1:raise relation.RelationError('first cubic kept one/copy link')
    evaluate=lambda lc:sum(rho.get(column,0)*coefficient for column,coefficient in lc)%p
    u=evaluate(result['values']['u']);tv=5*u*u%p;den=(1+tv)%p
    if not den:raise relation.RelationError('first cubic native denominator impossible')
    rho[result['q']]=pow(den,-1,p)
    for step in result['steps']:
        if step['kind']=='square':rho[step['output']]=(evaluate(step['input'])**2-evaluate(step['remainder']))%p
        else:
            left,right=evaluate(step['left']),evaluate(step['right'])
            rho[step['output']]=(left*right-evaluate(step['remainder']))%p
            rho[step['auxiliary']]=(left-right)**2%p
    if any(evaluate(a)**2%p!=evaluate(b) for a,b in result['raw'].values()):
        raise relation.RelationError('first cubic constructed original row failed')
    x=-maps.C1*pow(den,-1,p)%p;g=((x+maps.C1)*x+maps.C2)*x%p
    if evaluate(result['values']['gx1'])!=g or not g:
        raise relation.RelationError('first cubic native/actual nonzero join failed')
    if any(rho.get(c,0)!=v for c,v in base.items() if c not in result['owned']):
        raise relation.RelationError('first cubic modified unowned shared column')
    return dict(assignment=rho,plan=result,native_input=u,native_first=g,proof=False,
                scope='native first inverse/cubic local rows only; full map and hash/source input join separate')


def generate(data,extracted,accepted_roles):
    from .generate_hash_round import linear,signed,_signature_audits
    result=plan(data,extracted,accepted_roles);recipe=result['recipe'];v=result['values'];q=result['q']
    copy=recipe['checked']['metadata']['constant_copy'];name='RuntimeTransferAssetMapFirstCubicConstruction'
    sources=[]
    for step in result['steps']:
        if step['kind']=='square':sources.append('.square '+linear(step['input'])+' '+linear(step['remainder'])+' '+str(step['output']))
        else:sources.append('.product '+linear(step['left'])+' '+linear(step['right'])+' '+linear(step['remainder'])+' '+str(step['output'])+' '+str(step['auxiliary']))
    source=f'''import ShielddSecurity.RuntimeElligatorAlgebra
import ShielddSecurity.CompilerOrder
import ShielddSecurity.CompilerSignedCompletion
import ShielddSecurity.PoseidonCompletion
import ShielddSecurity.ScalarRows
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact metadata SHA256 {recipe['checked']['metadata_sha256']}.
-- Native first inverse and cubic; no per-input desired root/curve premise.
def modulus : Nat := {maps.P}
def input : Linear := {linear(v['u'])}
def tv : Linear := {linear(v['tv'])}
def denominator : Linear := {linear(v['den1'])}
def firstX : Linear := {linear(v['x1'])}
def firstG : Linear := {linear(v['gx1'])}
def inverseTarget : Linear := {linear(result['quotient']['output'])}
def kept : List Nat := {sorted({0,1,2,copy,q,*[c for c,_ in v['u']]})}
def steps : List CompilerCompletion.Step := [
'''+',\n'.join(sources)+f''']
def materialRows : List Row := CompilerCompletion.emitted steps
def expectedRows : List Row := materialRows ++ [⟨Compiler.subtract inverseTarget [(0,1)],[]⟩,⟨[],[]⟩]
def originalRowIndices : List Nat := {result['indices']}
def rawRows : List Row := [
'''+',\n'.join('⟨'+linear(a)+','+linear(b)+'⟩' for a,b in result['raw'].values())+f''']
variable {{F : Type}} [Field F] [CharP F modulus]
def nativeInput (rho : Nat → F) : F := eval rho input
def nativeTv (rho : Nat → F) : F := 5 * nativeInput rho * nativeInput rho
def nativeInverse (rho : Nat → F) : F := (1 + nativeTv rho)⁻¹
def nativeX (rho : Nat → F) : F := -(RuntimeElligatorAlgebra.c1 : F) * nativeInverse rho
def nativeFirst (rho : Nat → F) : F := Elligator.cubic
  (RuntimeElligatorAlgebra.c1 : F) (RuntimeElligatorAlgebra.c2 : F) (nativeX rho)
def seed (rho : Nat → F) : Nat → F := patchAssignment rho (fun _ => nativeInverse rho) [{q}]
def completeAssignment (rho : Nat → F) : Nat → F := CompilerCompletion.run (seed rho) steps

theorem ordered_checked : CompilerOrder.checkOrder kept [] steps = true := by decide
theorem ordered : CompilerCompletion.Topological kept [] steps := CompilerOrder.checked_order kept [] steps ordered_checked
theorem material_complete (rho : Nat → F) : Satisfies (completeAssignment rho) materialRows := by
  have legal : CompilerCompletion.Legal (seed rho) steps := by
    simp only [steps,CompilerCompletion.Legal,CompilerCompletion.Step.Legal,and_self]
  simpa only [List.nil_append] using CompilerCompletion.run_complete (seed rho) steps kept [] ordered legal
    (by intro row member; cases member)
theorem writes_subset_checked : (PoseidonCompletion.writes steps).all
    (fun column => decide (column ∈ {result['owned']})) = true := by decide
theorem preserves (rho : Nat → F) (column : Nat) (outside : column ∉ {result['owned']}) :
    completeAssignment rho column = rho column := by
  unfold completeAssignment seed
  rw [PoseidonCompletion.run_outside _ steps column (by
    intro written
    exact outside (of_decide_eq_true (List.all_eq_true.mp writes_subset_checked column written)))]
  exact patchAssignment_preserves rho _ [{q}] column (by
    simp only [List.mem_singleton]
    intro same
    apply outside
    subst column
    decide)
theorem input_value (rho : Nat → F) : eval (completeAssignment rho) input = nativeInput rho := by
  apply eval_agrees
  intro term member
  apply preserves
  have fresh : input.all (fun term => decide (term.1 ∉ {result['owned']})) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp fresh term member)
theorem inverse_value (rho : Nat → F) : completeAssignment rho {q} = nativeInverse rho := by
  unfold completeAssignment
  rw [PoseidonCompletion.run_outside (seed rho) steps {q} (by decide)]
  simp only [seed,patchAssignment,List.mem_singleton,if_true]
'''
    exports=['ordered_checked','ordered','material_complete','writes_subset_checked','preserves','input_value','inverse_value']
    for product in result['products']:
        cert=product['certificate'];a,b=(product['right'],product['left']) if cert.get('swapped') else (product['left'],product['right'])
        if cert['kind']=='product':datum='.product '+linear(cert['auxiliary'])
        elif cert['kind']=='square':datum='.square'
        else:raise relation.RelationError('first cubic source certificate must be material')
        label=product['label']+'_product'
        source+=f'''theorem {label} (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) :
    eval (completeAssignment rho) {linear(product['target'])} =
      eval (completeAssignment rho) {linear(product['left'])} * eval (completeAssignment rho) {linear(product['right'])} := by
  have finalOne : completeAssignment rho 0 = 1 := (preserves rho 0 (by decide)).trans one
  have actual := ScalarRows.checked_product_sound (completeAssignment rho) finalOne four
    materialRows (material_complete rho) {linear(a)} {linear(b)} {linear(product['target'])} ({datum}) (by decide)
  {'simpa only [mul_comm] using actual' if cert.get('swapped') else 'exact actual'}
'''
        exports.append(label)
    source+=f'''theorem tv_value (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) :
    eval (completeAssignment rho) tv = nativeTv rho := by
  have actual := tv_product rho one four
  change eval (completeAssignment rho) tv =
    eval (completeAssignment rho) {linear(maps._scale(v['u'],5))} * eval (completeAssignment rho) input at actual
  have scaled := Compiler.canonical_equal (completeAssignment rho) {linear(maps._scale(v['u'],5))}
    (scaleLinear 5 input) (by decide)
  rw [scaled,eval_scale,input_value] at actual
  simpa only [nativeTv,Int.cast_ofNat] using actual
theorem first_x_value (rho : Nat → F) : eval (completeAssignment rho) firstX = nativeX rho := by
  have actual := Compiler.canonical_equal (completeAssignment rho) firstX
    (scaleLinear (-RuntimeElligatorAlgebra.c1) [({q},1)]) (by decide)
  simpa only [eval_scale,eval,Int.cast_neg,Int.cast_one,one_mul,add_zero,inverse_value,nativeX] using actual
theorem first_g_value (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) :
    eval (completeAssignment rho) firstG = nativeFirst rho := by
  have first := first_product rho one four
  have second := cubic_product rho one four
  change eval (completeAssignment rho) {linear(result['products'][1]['target'])} =
    eval (completeAssignment rho) {linear(result['products'][1]['left'])} * eval (completeAssignment rho) firstX at first
  change eval (completeAssignment rho) firstG =
    eval (completeAssignment rho) {linear(result['products'][2]['left'])} * eval (completeAssignment rho) firstX at second
  have finalOne : completeAssignment rho 0 = 1 := (preserves rho 0 (by decide)).trans one
  have firstAdd := Compiler.canonical_equal (completeAssignment rho) {linear(result['products'][1]['left'])}
    (firstX ++ [(0,RuntimeElligatorAlgebra.c1)]) (by decide)
  have secondAdd := Compiler.canonical_equal (completeAssignment rho) {linear(result['products'][2]['left'])}
    ({linear(result['products'][1]['target'])} ++ [(0,RuntimeElligatorAlgebra.c2)]) (by decide)
  rw [eval_append] at firstAdd secondAdd
  have c1Value : eval (completeAssignment rho) [(0,RuntimeElligatorAlgebra.c1)] = (RuntimeElligatorAlgebra.c1 : F) := by simp only [eval,finalOne,mul_one,add_zero]
  have c2Value : eval (completeAssignment rho) [(0,RuntimeElligatorAlgebra.c2)] = (RuntimeElligatorAlgebra.c2 : F) := by simp only [eval,finalOne,mul_one,add_zero]
  rw [c1Value] at firstAdd
  rw [c2Value] at secondAdd
  rw [firstAdd,first_x_value] at first
  rw [secondAdd,first,first_x_value] at second
  simpa only [nativeFirst,Elligator.cubic] using second
'''
    exports+=['tv_value','first_x_value','first_g_value']
    source+=f'''theorem native_denominator_nonzero [Fintype F]
    (cardinality : Fintype.card F = modulus) (rho : Nat → F) :
    1 + nativeTv rho ≠ 0 := by
  have reduced := Compiler.coefficient_mod (F := F) (p := modulus) (-5)
  have checked : (-5 : Int) % (modulus : Int) = RuntimeElligatorParameters.negative_z := by decide
  rw [checked] at reduced
  have coefficient : (RuntimeElligatorParameters.negative_z : F) = -(5 : F) := by
    simpa only [Int.cast_neg,Int.cast_ofNat] using reduced
  have nonsquare := RuntimeElligatorParameters.negative_z_nonsquare (F := F) cardinality
  rw [coefficient] at nonsquare
  exact Elligator.first_denominator_nonzero (5 : F) (nativeInput rho) nonsquare

theorem native_coordinate [Fintype F] (cardinality : Fintype.card F = modulus)
    (rho : Nat → F) : (1 + nativeTv rho) * nativeX rho = -(RuntimeElligatorAlgebra.c1 : F) := by
  calc
    _ = -(RuntimeElligatorAlgebra.c1 : F) * ((1 + nativeTv rho) * nativeInverse rho) := by
      unfold nativeX
      ring
    _ = -(RuntimeElligatorAlgebra.c1 : F) := by
      rw [nativeInverse,mul_inv_cancel₀ (native_denominator_nonzero cardinality rho)]
      exact mul_one _

theorem native_first_nonzero [Fintype F] (cardinality : Fintype.card F = modulus)
    (rho : Nat → F) : nativeFirst rho ≠ 0 :=
  RuntimeElligatorAlgebra.first_cubic_nonzero cardinality (nativeX rho) (nativeTv rho)
    (native_coordinate cardinality rho)

theorem first_g_nonzero [Fintype F] (cardinality : Fintype.card F = modulus)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) :
    eval (completeAssignment rho) firstG ≠ 0 := by
  rw [first_g_value rho one four]
  exact native_first_nonzero cardinality rho

theorem denominator_value (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) :
    eval (completeAssignment rho) denominator = 1 + nativeTv rho := by
  have actual := Compiler.canonical_equal (completeAssignment rho) denominator
    ([(0,1)] ++ tv) (by decide)
  have finalOne : completeAssignment rho 0 = 1 := (preserves rho 0 (by decide)).trans one
  simpa only [eval_append,eval,finalOne,Int.cast_one,one_mul,add_zero,tv_value rho one four] using actual

theorem inverse_target_value [Fintype F] (cardinality : Fintype.card F = modulus)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) :
    eval (completeAssignment rho) inverseTarget = 1 := by
  have actual := inverseProduct_product rho one four
  change eval (completeAssignment rho) inverseTarget =
    eval (completeAssignment rho) [({q},1)] * eval (completeAssignment rho) denominator at actual
  have qValue : eval (completeAssignment rho) [({q},1)] = nativeInverse rho := by
    simp only [eval,Int.cast_one,one_mul,add_zero,inverse_value]
  rw [qValue,denominator_value rho one four] at actual
  exact actual.trans (inv_mul_cancel₀ (native_denominator_nonzero cardinality rho))

theorem expected_complete [Fintype F] (cardinality : Fintype.card F = modulus)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) :
    Satisfies (completeAssignment rho) expectedRows := by
  intro row member
  rcases List.mem_append.mp member with material | boundary
  · exact material_complete rho row material
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at boundary
    rcases boundary with rfl | rfl
    · have finalOne : completeAssignment rho 0 = 1 := (preserves rho 0 (by decide)).trans one
      simp only [Square,Compiler.eval_subtract,inverse_target_value cardinality rho one four,
        eval,finalOne,Int.cast_one,one_mul,add_zero,sub_self,zero_mul]
    · simp only [Square,eval,zero_mul]

theorem coverage_checked : rawRows.all (fun actual => expectedRows.any (fun expected => decide (
    (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
     Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) =
       Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b))) = true := by decide

theorem coverage : ∀ actual ∈ rawRows, ∃ expected ∈ expectedRows,
    (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
     Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) =
       Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp (List.all_eq_true.mp coverage_checked actual member)
  exact ⟨expected,present,of_decide_eq_true equations⟩

theorem complete_rows [Fintype F] (cardinality : Fintype.card F = modulus)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (linked : rho {copy} = rho 0) : Satisfies (completeAssignment rho) rawRows := by
  have finalLinked : completeAssignment rho {copy} = completeAssignment rho 0 := by
    rw [preserves rho {copy} (by decide),preserves rho 0 (by decide),linked]
  exact CompilerSignedCompletion.original_rows (completeAssignment rho) expectedRows rawRows {copy}
    finalLinked (expected_complete cardinality rho one four) coverage
'''
    exports+=['native_denominator_nonzero','native_coordinate','native_first_nonzero','first_g_nonzero',
              'denominator_value','inverse_target_value','expected_complete','coverage_checked','coverage','complete_rows']
    source+=''.join('#print axioms '+export+'\n' for export in exports)
    return name,_signature_audits(source+'end ShielddSecurity.'+name+'\n')
