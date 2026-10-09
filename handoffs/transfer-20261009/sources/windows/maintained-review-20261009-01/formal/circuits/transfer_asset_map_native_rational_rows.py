"""Three actual total-inverse assertions from computed native map witnesses."""
from . import transfer_asset_map as maps,transfer_asset_map_completion as completion
from . import transfer_arithmetic as arithmetic,transfer_relation as relation
from .transfer_balance_rows import combine


def plan(data,extracted,accepted_roles):
    recipe=completion.plan(data,extracted,accepted_roles);checked=recipe['checked'];v=checked['values']
    def product(label,a,b,target=None):
        choices=[(node,out) for node,left,right,out in checked['nonlinear']
                 if ((a,b)==(left,right) or (b,a)==(left,right)) and (target is None or out==target)]
        if len(choices)!=1:raise relation.RelationError('native rational exact product '+label)
        node,out=choices[0];cert=arithmetic.product_certificate(a,b,out,recipe['normalized'])
        if cert['kind']!='product':raise relation.RelationError('native rational original two-row product shape')
        matches=[i for i,step in enumerate(recipe['steps']) if step['rows']==cert['rows']]
        if len(matches)!=1:raise relation.RelationError('native rational actual owned product allocation')
        return dict(label=label,node=node,left=a,right=b,target=out,certificate=cert,position=matches[0])
    products=[product('selectX',v['square'],combine(v['x1'],v['x2'],-1)),
              product('denominator',v['plus'],v['t'],v['den']),
              product('inverseProduct',v['den'],v['inv'],checked['products'][1]),
              product('denominatorZero',v['den'],v['zero'],checked['products'][2]),
              product('inverseZero',v['inv'],v['zero'],checked['products'][3])]
    material=sorted({i for item in products for i in item['certificate']['rows']})
    expected=[(combine(checked['products'][1],combine(maps.ONE,v['zero'],-1),-1),()),
              (checked['products'][2],()),(checked['products'][3],())]
    indices=[]
    for a,b in expected:
        matches=[i for i,row in recipe['normalized'].items() if row in ((a,b),(maps._scale(a,-1),b))]
        if len(matches)!=1:raise relation.RelationError('native rational exact original assertion')
        indices.append(matches[0])
    chunks=sorted({product['position']//8 for product in products})
    if len(chunks)>3 or len(material)!=10 or set(indices)&set(recipe['material_rows']):
        raise relation.RelationError('native rational bounded original row partition')
    return dict(recipe=recipe,products=products,material=material,chunks=chunks,indices=indices,
                expected=expected,raw={i:recipe['raw'][i] for i in indices})


def generate(data,extracted,accepted_roles):
    return _from_checked(plan(data,extracted,accepted_roles))


def _from_checked(result):
    """Render only the already checked bounded native rational layout."""
    from .generate_hash_round import linear,_signature_audits
    recipe=result['recipe'];v=recipe['checked']['values']
    native='RuntimeTransferAssetMapNativeSeeds';first='RuntimeTransferAssetMapNativeFirstRows'
    core='RuntimeTransferAssetMapFirstCubicConstruction';numeric='RuntimeTransferAssetMapNumericConstruction'
    chunks=['RuntimeTransferAssetMapMaterialization'+str(i) for i in result['chunks']]
    copy=recipe['checked']['metadata']['constant_copy']
    name='RuntimeTransferAssetMapNativeRationalRows'
    union=chunks[-1]+'.rawRows'
    for chunk in reversed(chunks[:-1]):union=chunk+'.rawRows ++ ('+union+')'
    source=f'''import ShielddSecurity.{first}
'''+''.join('import ShielddSecurity.'+chunk+'\n' for chunk in chunks)+f'''import ShielddSecurity.CompilerSignedCompletion
set_option maxHeartbeats 350000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact actual metadata SHA256 {recipe['checked']['metadata_sha256']}.
-- Total inverse includes zero; no rational denominator nonzero premise.
abbrev modulus := {native}.modulus
def originalRowIndices : List Nat := {result['indices']}
def rawMaterialRows : List Row := [
'''+',\n'.join('⟨'+linear(recipe['raw'][i][0])+','+linear(recipe['raw'][i][1])+'⟩' for i in result['material'])+f''']
def sourceRawRows : List Row := {union}
def materialRows : List Row := Compiler.unoutlineRows {copy} rawMaterialRows
def rawRows : List Row := [
'''+',\n'.join('⟨'+linear(a)+','+linear(b)+'⟩' for a,b in result['raw'].values())+''']
def expectedRows : List Row := [
'''+',\n'.join('⟨'+linear(a)+','+linear(b)+'⟩' for a,b in result['expected'])+f''']
variable {{F : Type}} [Field F] [CharP F modulus] [DecidableEq F]
abbrev finalAssignment (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) := {native}.completeAssignment codec api rho
theorem material_subset_checked : rawMaterialRows.all (fun row => decide (row ∈ sourceRawRows)) = true := by decide
theorem material_subset : ∀ row ∈ rawMaterialRows, row ∈ sourceRawRows := by
  intro row member
  exact of_decide_eq_true (List.all_eq_true.mp material_subset_checked row member)
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
  have raw := sourceRows actual (material_subset actual present)
  simpa only [Compiler.eval_unoutline _ {copy} _ ({first}.final_link codec api rho linked)] using raw
'''
    exports=['material_subset_checked','material_subset','material_complete']
    for item in result['products']:
        cert=item['certificate'];a,b=item['left'],item['right'];left,right=(b,a) if cert.get('swapped') else (a,b)
        source+=f'''theorem {item['label']}_product (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    eval (finalAssignment codec api rho) {linear(item['target'])} =
      eval (finalAssignment codec api rho) {linear(a)} * eval (finalAssignment codec api rho) {linear(b)} := by
  have actual := ScalarRows.checked_product_sound (finalAssignment codec api rho)
    ({first}.final_one codec api rho one) four materialRows (material_complete codec api rho linked)
    {linear(left)} {linear(right)} {linear(item['target'])} (.product {linear(cert['auxiliary'])}) (by decide)
  simpa only [mul_comm] using actual
'''
        exports.append(item['label']+'_product')
    source+=f'''theorem selected_x_value (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    eval (finalAssignment codec api rho) {linear(v['x'])} = {native}.nativeSelectedX api rho := by
  have alternative := Compiler.canonical_equal (finalAssignment codec api rho) {linear(v['x2'])}
    (scaleLinear (-1) {core}.firstX ++ [(0,-RuntimeElligatorAlgebra.c1)]) (by decide)
  have constant : eval (finalAssignment codec api rho) [(0,-RuntimeElligatorAlgebra.c1)] =
      -(RuntimeElligatorAlgebra.c1 : F) := by
    simp only [eval,Int.cast_neg,{first}.final_one codec api rho one,mul_one,add_zero]
  rw [eval_append,eval_scale,{first}.first_x_value,constant] at alternative
  have selected := selectX_product codec api rho one four linked
  have difference := Compiler.canonical_equal (finalAssignment codec api rho) {linear(result['products'][0]['right'])}
    (Compiler.subtract {core}.firstX {linear(v['x2'])}) (by decide)
  rw [difference,Compiler.eval_subtract,{first}.first_x_value,alternative] at selected
  have choiceValue : eval (finalAssignment codec api rho) {linear(v['square'])} =
      if {native}.nativeChoice api rho then 1 else 0 := by
    simp only [eval,Int.cast_one,one_mul,add_zero,{native}.final_choice_value]
  rw [choiceValue] at selected
  have combined := Compiler.canonical_equal (finalAssignment codec api rho) {linear(v['x'])}
    ({linear(v['x2'])} ++ {linear(result['products'][0]['target'])}) (by decide)
  rw [combined,eval_append,alternative,selected]
  unfold {native}.nativeSelectedX
  cases option : {native}.nativeChoice api rho <;>
    simp only [option,Bool.false_eq_true,if_true,if_false,Int.cast_neg,Int.cast_one] <;> ring

theorem s_value (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    eval (finalAssignment codec api rho) {linear(v['s'])} =
      (RuntimeElligatorAlgebra.k : F) * {native}.nativeSelectedX api rho := by
  have actual := Compiler.canonical_equal (finalAssignment codec api rho) {linear(v['s'])}
    (scaleLinear RuntimeElligatorAlgebra.k {linear(v['x'])}) (by decide)
  simpa only [eval_scale,selected_x_value codec api rho one four linked] using actual
theorem t_value (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) : eval (finalAssignment codec api rho) {linear(v['t'])} =
      (RuntimeElligatorAlgebra.k : F) * {native}.nativeY codec api rho := by
  have actual := Compiler.canonical_equal (finalAssignment codec api rho) {linear(v['t'])}
    (scaleLinear RuntimeElligatorAlgebra.k {linear(v['y'])}) (by decide)
  simpa only [eval_scale,eval,Int.cast_one,one_mul,add_zero,{native}.final_selectedRoot_value] using actual
theorem plus_value (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    eval (finalAssignment codec api rho) {linear(v['plus'])} =
      (RuntimeElligatorAlgebra.k : F) * {native}.nativeSelectedX api rho + 1 := by
  have actual := Compiler.canonical_equal (finalAssignment codec api rho) {linear(v['plus'])}
    ({linear(v['s'])} ++ [(0,1)]) (by decide)
  rw [eval_append,s_value codec api rho one four linked] at actual
  simpa only [eval,
    {first}.final_one codec api rho one,Int.cast_one,one_mul,add_zero] using actual
theorem denominator_value (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    eval (finalAssignment codec api rho) {linear(v['den'])} = {native}.nativeRationalDenominator codec api rho := by
  have actual := denominator_product codec api rho one four linked
  rw [plus_value codec api rho one four linked,t_value] at actual
  exact actual
theorem inverse_value (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) : eval (finalAssignment codec api rho) {linear(v['inv'])} =
      ({native}.nativeRationalDenominator codec api rho)⁻¹ := by
  simp only [eval,Int.cast_one,one_mul,add_zero,{native}.final_totalInverse_value]
theorem zero_value (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) : eval (finalAssignment codec api rho) {linear(v['zero'])} =
      if {native}.nativeRationalDenominator codec api rho = 0 then 1 else 0 := by
  simp only [eval,Int.cast_one,one_mul,add_zero,{native}.final_zero_value]
theorem computed_constraints (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    eval (finalAssignment codec api rho) {linear(recipe['checked']['products'][1])} =
      1 - eval (finalAssignment codec api rho) {linear(v['zero'])} ∧
    eval (finalAssignment codec api rho) {linear(recipe['checked']['products'][2])} = 0 ∧
    eval (finalAssignment codec api rho) {linear(recipe['checked']['products'][3])} = 0 := by
  rw [inverseProduct_product codec api rho one four linked,denominatorZero_product codec api rho one four linked,
    inverseZero_product codec api rho one four linked,denominator_value codec api rho one four linked,inverse_value,zero_value]
  have total : (if {native}.nativeRationalDenominator codec api rho = 0 then (0 : F)
      else ({native}.nativeRationalDenominator codec api rho)⁻¹) = ({native}.nativeRationalDenominator codec api rho)⁻¹ := by
    by_cases exceptional : {native}.nativeRationalDenominator codec api rho = 0
    · simp only [exceptional,inv_zero,if_true]
    · simp only [if_neg exceptional]
  have legal := Elligator.inverse_constraints_complete ({native}.nativeRationalDenominator codec api rho)
  dsimp only at legal
  rw [total] at legal
  exact legal
'''
    exports+=['selected_x_value','s_value','t_value','plus_value','denominator_value','inverse_value','zero_value','computed_constraints']
    delta=result['expected'][0][0];prod=recipe['checked']['products'];zeroTarget=combine(maps.ONE,v['zero'],-1)
    source+=f'''theorem expected_complete (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    Satisfies (finalAssignment codec api rho) expectedRows := by
  have legal := computed_constraints codec api rho one four linked
  have delta := Compiler.canonical_equal (finalAssignment codec api rho) {linear(delta)}
    (Compiler.subtract {linear(prod[1])} {linear(zeroTarget)}) (by decide)
  have target := Compiler.canonical_equal (finalAssignment codec api rho) {linear(zeroTarget)}
    (Compiler.subtract [(0,1)] {linear(v['zero'])}) (by decide)
  have oneValue : eval (finalAssignment codec api rho) [(0,1)] = 1 := by
    simp only [eval,Int.cast_one,one_mul,add_zero,{first}.final_one codec api rho one]
  intro row member
  simp only [expectedRows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · change Square (eval (finalAssignment codec api rho) {linear(delta)}) 0
    rw [delta,Compiler.eval_subtract,target,Compiler.eval_subtract,oneValue,legal.1]
    simp only [sub_self,Square,zero_mul]
  · change Square (eval (finalAssignment codec api rho) {linear(prod[2])}) 0
    rw [legal.2.1]
    exact zero_mul 0
  · change Square (eval (finalAssignment codec api rho) {linear(prod[3])}) 0
    rw [legal.2.2]
    exact zero_mul 0
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
theorem complete_rows (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) : Satisfies (finalAssignment codec api rho) rawRows :=
  CompilerSignedCompletion.original_rows (finalAssignment codec api rho) expectedRows rawRows {copy}
    ({first}.final_link codec api rho linked) (expected_complete codec api rho one four linked) coverage
'''
    exports+=['expected_complete','coverage_checked','coverage','complete_rows']
    source+=''.join('#print axioms '+export+'\n' for export in exports)
    return name,_signature_audits(source+'end ShielddSecurity.'+name+'\n')
