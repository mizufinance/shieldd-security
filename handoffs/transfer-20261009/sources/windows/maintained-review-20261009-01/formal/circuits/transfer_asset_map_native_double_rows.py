"""Three actual constructive map doubles, with derived inverse assertions."""
from . import transfer_asset_map as maps,transfer_asset_map_completion as completion
from . import transfer_asset_map_cofactor as cofactor,transfer_arithmetic as arithmetic
from . import transfer_relation as relation
from .transfer_balance_rows import combine


def plan(data,extracted,accepted_roles,stage):
    if type(stage)is not int or not 0<=stage<3:raise relation.RelationError('native double stage0..2')
    recipe=completion.plan(data,extracted,accepted_roles);checked=recipe['checked'];point=cofactor._plan(checked,stage)
    products=[]
    for label,(_,node,a,b,out) in point['selected'].items():
        cert=arithmetic.product_certificate(a,b,out,recipe['normalized'])
        matches=[i for i,step in enumerate(recipe['steps']) if step['rows']==cert['rows']]
        if len(matches)!=1:raise relation.RelationError('native double exact materialized source product')
        products.append(dict(label=label,node=node,left=a,right=b,target=out,certificate=cert,position=matches[0]))
    quotient=maps.certificates(data,extracted,accepted_roles)['quotients'][stage+1]
    matches=[i for i,step in enumerate(recipe['steps']) if step['rows']==quotient['rows'][:2]]
    if len(matches)!=1 or quotient['kind']!='product':raise relation.RelationError('native double exact original quotient product')
    products.append(dict(label='quotient',left=quotient['quotient'],right=quotient['denominator'],target=quotient['output'],
                         certificate=quotient,position=matches[0]))
    material=sorted({i for item in products for i in item['certificate']['rows'][:(1 if item['certificate']['kind']=='square' else 2)]})
    chunks=sorted({item['position']//8 for item in products})
    delta=combine(quotient['output'],maps.ONE,-1)
    assertions=[i for i,row in recipe['normalized'].items() if row in ((delta,()),(maps._scale(delta,-1),()))]
    if len(assertions)!=1 or len(material)>22 or len(chunks)>3:
        raise relation.RelationError('native double bounded material/original assertion partition')
    return dict(recipe=recipe,stage=stage,point=point,products=products,quotient=quotient,
                material=material,chunks=chunks,assertion=assertions[0])


def generate(data,extracted,accepted_roles,stage):
    return _from_checked(plan(data,extracted,accepted_roles,stage))


def _from_checked(result):
    """Render bounded previously checked layout; public entry retains full checks."""
    from .generate_hash_round import linear,_signature_audits
    stage=result['stage'];recipe=result['recipe'];point=result['point'];copy=recipe['checked']['metadata']['constant_copy']
    name='RuntimeTransferAssetMapNativeDouble'+str(stage);native='RuntimeTransferAssetMapNativeSeeds'
    first='RuntimeTransferAssetMapNativeFirstRows';numeric='RuntimeTransferAssetMapNumericConstruction'
    predecessor='RuntimeTransferAssetMapNativeImageRows' if stage==0 else 'RuntimeTransferAssetMapNativeDouble'+str(stage-1)
    native_input='nativeImage' if stage==0 else 'nativePoint'+str(stage)
    chunks=['RuntimeTransferAssetMapMaterialization'+str(i) for i in result['chunks']]
    union=chunks[-1]+'.rawRows'
    for chunk in reversed(chunks[:-1]):union=chunk+'.rawRows ++ ('+union+')'
    actual=recipe['raw'][result['assertion']];qtarget=result['quotient']['output']
    source=f'''import ShielddSecurity.{predecessor}
'''+''.join('import ShielddSecurity.'+chunk+'\n' for chunk in chunks)+f'''import ShielddSecurity.CompilerSignedCompletion
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact actual metadata SHA256 {recipe['checked']['metadata_sha256']}.
-- Original cofactor double{stage}; inverse legality derives computed native curve.
abbrev modulus := {native}.modulus
def originalMaterialRowIndices : List Nat := {result['material']}
def originalAssertionRow : Nat := {result['assertion']}
def rawMaterialRows : List Row := [
'''+',\n'.join('⟨'+linear(recipe['raw'][i][0])+','+linear(recipe['raw'][i][1])+'⟩' for i in result['material'])+f''']
def sourceRawRows : List Row := {union}
def materialRows : List Row := Compiler.unoutlineRows {copy} rawMaterialRows
def rawRows : List Row := [⟨{linear(actual[0])},{linear(actual[1])}⟩]
def expectedRows : List Row := [⟨Compiler.subtract {linear(qtarget)} [(0,1)],[]⟩]
'''
    for label in ('xx','yy','dt','plus','minus','divisor','inverse'):
        source+='def '+label+' : Linear := '+linear(point[label])+'\n'
    for label in ('input','output'):
        x,y=point[label]
        source+=f'def {label} {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F := ⟨eval rho {linear(x)},eval rho {linear(y)}⟩\n'
    source+=f'''variable {{F : Type}} [Field F] [CharP F modulus] [DecidableEq F]
abbrev finalAssignment (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) := {native}.completeAssignment codec api rho
theorem material_subset_checked : rawMaterialRows.all (fun row => decide (row ∈ sourceRawRows)) = true := by decide
theorem material_complete (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (linked : rho {copy} = rho 0) : Satisfies (finalAssignment codec api rho) materialRows := by
  have completed := {native}.numeric_complete codec api rho linked
'''
    for i,chunk in zip(result['chunks'],chunks):
        present='List.mem_cons_self'
        for _ in range(i):present='(List.mem_cons_of_mem _ '+present+')'
        source+=f'''  have chunk{i}Member : {chunk}.rawRows ∈ {numeric}.rawChunks := by
    exact {present}
'''
    source+='''  have sourceRows : Satisfies (finalAssignment codec api rho) sourceRawRows := by
    intro row member
    simp only [sourceRawRows,List.mem_append] at member
'''
    if len(chunks)>1:source+='    rcases member with '+' | '.join('case'+str(i) for i in result['chunks'])+'\n'
    for i,chunk in zip(result['chunks'],chunks):
        source+=('    · ' if len(chunks)>1 else '    ')+f'exact completed row (List.mem_flatten.mpr ⟨{chunk}.rawRows,chunk{i}Member,'+('case'+str(i) if len(chunks)>1 else 'member')+'⟩)\n'
    source+=f'''  intro row member
  obtain ⟨actual,present,rfl⟩ := List.mem_map.mp member
  have raw := sourceRows actual (of_decide_eq_true (List.all_eq_true.mp material_subset_checked actual present))
  simpa only [Compiler.eval_unoutline _ {copy} _ ({first}.final_link codec api rho linked)] using raw
'''
    exports=['material_subset_checked','material_complete']
    common=f'''(codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0)'''
    for item in result['products']:
        a,b=item['left'],item['right'];cert=item['certificate'];left,right=(b,a) if cert.get('swapped') else (a,b)
        if cert['kind']=='square':datum='.square'
        elif cert['kind']=='product':datum='.product '+linear(cert['auxiliary'])
        else:raise relation.RelationError('native double supported original product encoding only')
        source+=f'''theorem {item['label']}_product {common} :
    eval (finalAssignment codec api rho) {linear(item['target'])} =
      eval (finalAssignment codec api rho) {linear(a)} * eval (finalAssignment codec api rho) {linear(b)} := by
  have actual := ScalarRows.checked_product_sound (finalAssignment codec api rho)
    ({first}.final_one codec api rho one) four materialRows (material_complete codec api rho linked)
    {linear(left)} {linear(right)} {linear(item['target'])} ({datum}) (by decide)
  simpa only [mul_comm] using actual
'''
        exports.append(item['label']+'_product')
    source+=f'''theorem input_native [Fintype F] (cardinality : Fintype.card F = modulus) {common} :
    input (finalAssignment codec api rho) = {native}.{native_input} codec api rho := by
'''
    if stage==0:source+=f'  exact {predecessor}.native_image codec api rho one four linked\n'
    else:source+=f'  exact {predecessor}.output_native cardinality codec api rho one four linked\n'
    source+=f'''theorem delta_value {common} :
    eval (finalAssignment codec api rho) dt =
      Group.delta (RuntimeJubjub.d : F) (input (finalAssignment codec api rho)) (input (finalAssignment codec api rho)) := by
  have xxValue := xx_product codec api rho one four linked
  have yyValue := yy_product codec api rho one four linked
  have deltaValue := delta_product codec api rho one four linked
  have scaled := Compiler.canonical_equal (finalAssignment codec api rho) dt
    (scaleLinear RuntimeJubjub.d {linear(point['delta_base'])}) (by decide)
  rw [eval_scale,deltaValue,xxValue,yyValue] at scaled
  calc
    _ = _ := scaled
    _ = _ := by unfold Group.delta input; ring
theorem plus_value {common} :
    eval (finalAssignment codec api rho) plus = 1 +
      Group.delta (RuntimeJubjub.d : F) (input (finalAssignment codec api rho)) (input (finalAssignment codec api rho)) := by
  have actual := Compiler.canonical_equal (finalAssignment codec api rho) plus ([(0,1)] ++ dt) (by decide)
  have unit : eval (finalAssignment codec api rho) [(0,1)] = 1 := by
    simp only [eval,Int.cast_one,one_mul,add_zero,{first}.final_one codec api rho one]
  rw [eval_append,unit,delta_value codec api rho one four linked] at actual
  exact actual
theorem minus_value {common} :
    eval (finalAssignment codec api rho) minus = 1 -
      Group.delta (RuntimeJubjub.d : F) (input (finalAssignment codec api rho)) (input (finalAssignment codec api rho)) := by
  have actual := Compiler.canonical_equal (finalAssignment codec api rho) minus (Compiler.subtract [(0,1)] dt) (by decide)
  have unit : eval (finalAssignment codec api rho) [(0,1)] = 1 := by
    simp only [eval,Int.cast_one,one_mul,add_zero,{first}.final_one codec api rho one]
  rw [Compiler.eval_subtract,unit,delta_value codec api rho one four linked] at actual
  exact actual
theorem divisor_value [Fintype F] (cardinality : Fintype.card F = modulus) {common} :
    eval (finalAssignment codec api rho) divisor = {native}.nativeDivisor ({native}.{native_input} codec api rho) := by
  have actual := divisor_product codec api rho one four linked
  change eval (finalAssignment codec api rho) divisor = eval (finalAssignment codec api rho) plus *
    eval (finalAssignment codec api rho) minus at actual
  rw [plus_value codec api rho one four linked,minus_value codec api rho one four linked,
    input_native cardinality codec api rho one four linked] at actual
  exact actual
theorem inverse_value (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) :
    eval (finalAssignment codec api rho) inverse = ({native}.nativeDivisor ({native}.{native_input} codec api rho))⁻¹ := by
  simp only [inverse,eval,Int.cast_one,one_mul,add_zero,{native}.final_doubleInverse{stage}_value]
theorem quotient_target_value [Fintype F] (cardinality : Fintype.card F = modulus) {common} :
    eval (finalAssignment codec api rho) {linear(qtarget)} = 1 := by
  have actual := quotient_product codec api rho one four linked
  change eval (finalAssignment codec api rho) {linear(qtarget)} = eval (finalAssignment codec api rho) inverse *
    eval (finalAssignment codec api rho) divisor at actual
  rw [inverse_value,divisor_value cardinality codec api rho one four linked] at actual
  exact actual.trans (inv_mul_cancel₀ ({native}.quotient{stage+1}_denominator_nonzero cardinality codec api rho))
'''
    exports+=['input_native','delta_value','plus_value','minus_value','divisor_value','inverse_value','quotient_target_value']
    selected={item['label']:item for item in result['products']}
    source+=f'''theorem x_value {common} :
    (output (finalAssignment codec api rho)).x =
      Group.cross (input (finalAssignment codec api rho)) (input (finalAssignment codec api rho)) *
      (1 - Group.delta (RuntimeJubjub.d : F) (input (finalAssignment codec api rho)) (input (finalAssignment codec api rho))) *
      eval (finalAssignment codec api rho) inverse := by
  have actual := xOutput_product codec api rho one four linked
  have total := Compiler.checked_add_sound (finalAssignment codec api rho)
    {linear(selected['crossLeft']['target'])} {linear(selected['crossRight']['target'])}
    {linear(selected['xTimesMinus']['left'])} (by decide)
  rw [xTimesMinus_product codec api rho one four linked,total,
    crossLeft_product codec api rho one four linked,crossRight_product codec api rho one four linked] at actual
  have minusValue : eval (finalAssignment codec api rho) {linear(point['minus'])} =
      1 - Group.delta (RuntimeJubjub.d : F) (input (finalAssignment codec api rho))
        (input (finalAssignment codec api rho)) := minus_value codec api rho one four linked
  rw [minusValue] at actual
  calc
    _ = _ := actual
    _ = _ := by unfold Group.cross input inverse; ring
theorem y_value {common} :
    (output (finalAssignment codec api rho)).y =
      Group.diagonal (input (finalAssignment codec api rho)) (input (finalAssignment codec api rho)) *
      (1 + Group.delta (RuntimeJubjub.d : F) (input (finalAssignment codec api rho)) (input (finalAssignment codec api rho))) *
      eval (finalAssignment codec api rho) inverse := by
  have actual := yOutput_product codec api rho one four linked
  have total := Compiler.checked_add_sound (finalAssignment codec api rho) yy xx
    {linear(combine(point['yy'],point['xx']))} (by decide)
  rw [yTimesPlus_product codec api rho one four linked,total] at actual
  have xxValue := xx_product codec api rho one four linked
  have yyValue := yy_product codec api rho one four linked
  change eval (finalAssignment codec api rho) xx =
    eval (finalAssignment codec api rho) {linear(point['input'][0])} *
      eval (finalAssignment codec api rho) {linear(point['input'][0])} at xxValue
  change eval (finalAssignment codec api rho) yy =
    eval (finalAssignment codec api rho) {linear(point['input'][1])} *
      eval (finalAssignment codec api rho) {linear(point['input'][1])} at yyValue
  have plusValue : eval (finalAssignment codec api rho) {linear(point['plus'])} =
      1 + Group.delta (RuntimeJubjub.d : F) (input (finalAssignment codec api rho))
        (input (finalAssignment codec api rho)) := plus_value codec api rho one four linked
  rw [xxValue,yyValue,plusValue] at actual
  calc
    _ = _ := actual
    _ = _ := by unfold Group.diagonal input inverse; ring
theorem output_native [Fintype F] (cardinality : Fintype.card F = modulus) {common} :
    output (finalAssignment codec api rho) = {native}.nativePoint{stage+1} codec api rho := by
  have x := x_value codec api rho one four linked
  have y := y_value codec api rho one four linked
  rw [input_native cardinality codec api rho one four linked,inverse_value] at x y
  exact congrArg₂ Group.Point.mk x y
theorem coverage_checked : rawRows.all (fun actual => expectedRows.any (fun expected => decide (
    (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
     Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b))) = true := by decide
theorem coverage : ∀ actual ∈ rawRows, ∃ expected ∈ expectedRows,
    (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
     Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp (List.all_eq_true.mp coverage_checked actual member)
  exact ⟨expected,present,of_decide_eq_true equations⟩
theorem complete_rows [Fintype F] (cardinality : Fintype.card F = modulus) {common} :
    Satisfies (finalAssignment codec api rho) rawRows := by
  have expected : Satisfies (finalAssignment codec api rho) expectedRows := by
    intro row member
    simp only [expectedRows,List.mem_singleton] at member
    subst row
    have target := quotient_target_value cardinality codec api rho one four linked
    have unit : eval (finalAssignment codec api rho) [(0,1)] = 1 := by
      simp only [eval,Int.cast_one,one_mul,add_zero,{first}.final_one codec api rho one]
    rw [Compiler.eval_subtract,target,unit]
    simp only [eval,sub_self,Square,zero_mul]
  exact CompilerSignedCompletion.original_rows (finalAssignment codec api rho) expectedRows rawRows {copy}
    ({first}.final_link codec api rho linked) expected coverage
'''
    exports+=['x_value','y_value','output_native','coverage_checked','coverage','complete_rows']
    source+=''.join('#print axioms '+export+'\n' for export in exports)
    return name,_signature_audits(source+'end ShielddSecurity.'+name+'\n')
