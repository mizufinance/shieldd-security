"""Two original root assertions from actual constructed material LC values."""
from . import transfer_asset_map as maps,transfer_asset_map_completion as completion
from . import transfer_asset_map_native_first_rows as first,transfer_relation as relation
from . import transfer_arithmetic as arithmetic
from .transfer_balance_rows import combine


def plan(data,extracted,accepted_roles):
    recipe=completion.plan(data,extracted,accepted_roles);checked=recipe['checked'];v=checked['values']
    if checked['metadata']['schema']!='shieldd-transfer-asset-map-v2':
        raise relation.RelationError('native root rows require actual deferred-square metadata')
    by_rows={tuple(step['rows']):step for step in recipe['steps']}
    def product(label,a,b,target=None):
        choices=[(node,out) for node,left,right,out in checked['nonlinear']
                 if ((a,b)==(left,right) or (b,a)==(left,right)) and (target is None or out==target)]
        if len(choices)!=1:raise relation.RelationError('native root exact source product '+label)
        node,out=choices[0];cert=arithmetic.product_certificate(a,b,out,recipe['normalized'])
        return dict(label=label,node=node,left=a,right=b,target=out,certificate=cert)
    alternative=product('alternative',v['tv'],v['gx1'],v['gx2'])
    selected=product('selected',v['square'],combine(v['gx1'],v['gx2'],-1))
    qr=product('qr',v['square'],maps._scale(v['gx1'],-4))
    qr_square=next((step for step in recipe['steps'] if step['kind']=='square' and step['input']==v['qr_root']),None)
    aux_step=by_rows.get(tuple(qr['certificate']['rows'][:1]))
    if (qr_square is None or qr_square['remainder']!=maps._scale(v['gx1'],5)
        or ((qr_square['output'],1),)!=qr['target'] or aux_step is None or aux_step['kind']!='square'):
        raise relation.RelationError('native root exact QR square/fused difference allocation')
    squared=arithmetic.product_certificate(v['y'],v['y'],v['y_squared'],recipe['normalized'])
    if squared['kind']!='square' or len(squared['rows'])!=1:
        raise relation.RelationError('native root exact original selected asserted square')
    indices=[qr['certificate']['rows'][1],squared['rows'][0]]
    if set(indices)&set(recipe['material_rows']):raise relation.RelationError('native root assertions already materialized')
    return dict(recipe=recipe,products=[alternative,selected],qr=qr,qr_square=qr_square,aux_step=aux_step,
                indices=indices,raw={i:recipe['raw'][i] for i in indices},
                expected=[(qr['left']+qr['right'],qr['certificate']['auxiliary']+maps._scale(qr['target'],4)),
                          (v['y'],v['y_squared'])])


def generate(data,extracted,accepted_roles):
    return _from_checked(plan(data,extracted,accepted_roles))


def _from_checked(result):
    """Render a previously checked bounded row layout; public entry still checks it."""
    from .generate_hash_round import linear,_signature_audits
    recipe=result['recipe'];v=recipe['checked']['values']
    copy=recipe['checked']['metadata']['constant_copy'];name='RuntimeTransferAssetMapNativeRootRows'
    native='RuntimeTransferAssetMapNativeSeeds';first_name='RuntimeTransferAssetMapNativeFirstRows'
    core='RuntimeTransferAssetMapFirstCubicConstruction';chunk='RuntimeTransferAssetMapMaterialization0'
    numeric='RuntimeTransferAssetMapNumericConstruction';qr=result['qr'];aux=result['aux_step']
    source=f'''import ShielddSecurity.{first_name}
import ShielddSecurity.{chunk}
import ShielddSecurity.CompilerSignedCompletion
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact actual metadata SHA256 {recipe['checked']['metadata_sha256']}.
-- QR sum-square and selected square derive computed native roots, not row premises.
abbrev modulus := {native}.modulus
def originalRowIndices : List Nat := {result['indices']}
def rawRows : List Row := [
'''+',\n'.join('⟨'+linear(a)+','+linear(b)+'⟩' for a,b in result['raw'].values())+''']
def expectedRows : List Row := [
'''+',\n'.join('⟨'+linear(a)+','+linear(b)+'⟩' for a,b in result['expected'])+f''']
def materialRows : List Row := Compiler.unoutlineRows {copy} {chunk}.rawRows
variable {{F : Type}} [Field F] [CharP F modulus] [DecidableEq F]
abbrev finalAssignment (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) := {native}.completeAssignment codec api rho

theorem material_complete (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (linked : rho {copy} = rho 0) : Satisfies (finalAssignment codec api rho) materialRows := by
  have completed := {native}.numeric_complete codec api rho linked
  have chunkMember : {chunk}.rawRows ∈ {numeric}.rawChunks := by
    unfold {numeric}.rawChunks
    exact List.mem_cons_self
  intro row member
  obtain ⟨actual,present,rfl⟩ := List.mem_map.mp member
  have raw := completed actual (List.mem_flatten.mpr ⟨{chunk}.rawRows,chunkMember,present⟩)
  simpa only [Compiler.eval_unoutline _ {copy} _ ({first_name}.final_link codec api rho linked)] using raw
'''
    exports=['material_complete']
    for product in result['products']:
        cert=product['certificate'];a,b=product['left'],product['right'];left,right=(b,a) if cert.get('swapped') else (a,b)
        source+=f'''theorem {product['label']}_product (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    eval (finalAssignment codec api rho) {linear(product['target'])} =
      eval (finalAssignment codec api rho) {linear(a)} * eval (finalAssignment codec api rho) {linear(b)} := by
  have actual := ScalarRows.checked_product_sound (finalAssignment codec api rho)
    ({first_name}.final_one codec api rho one) four materialRows (material_complete codec api rho linked)
    {linear(left)} {linear(right)} {linear(product['target'])} (.product {linear(cert['auxiliary'])}) (by decide)
  simpa only [mul_comm] using actual
'''
        exports.append(product['label']+'_product')
    for label,step,target in [('qr',result['qr_square'],recipe['checked']['qr'][1]),
                               ('aux',aux,qr['certificate']['auxiliary'])]:
        source+=f'''theorem {label}_square (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) (linked : rho {copy} = rho 0) :
    eval (finalAssignment codec api rho) {linear(target)} =
      eval (finalAssignment codec api rho) {linear(step['input'])} * eval (finalAssignment codec api rho) {linear(step['input'])} :=
  Compiler.checked_square_sound (finalAssignment codec api rho) materialRows
    {linear(step['input'])} {linear(target)} (material_complete codec api rho linked) (by decide)
'''
        exports.append(label+'_square')
    source+=f'''theorem alternative_value (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    eval (finalAssignment codec api rho) {linear(v['gx2'])} = {core}.nativeTv rho * {core}.nativeFirst rho := by
  have actual := alternative_product codec api rho one four linked
  change eval ({first_name}.finalAssignment codec api rho) {linear(v['gx2'])} =
    eval ({first_name}.finalAssignment codec api rho) {core}.tv *
      eval ({first_name}.finalAssignment codec api rho) {core}.firstG at actual
  rw [{first_name}.tv_value codec api rho one four linked,{first_name}.first_g_value codec api rho one four linked] at actual
  exact actual

theorem qr_output_value (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    eval (finalAssignment codec api rho) {linear(qr['target'])} =
      {native}.nativeQr api rho * {native}.nativeQr api rho - 5 * {core}.nativeFirst rho := by
  have actual := qr_square codec api rho linked
  have target := Compiler.canonical_equal (finalAssignment codec api rho) {linear(recipe['checked']['qr'][1])}
    ({linear(qr['target'])} ++ scaleLinear 5 {core}.firstG) (by decide)
  have rootValue : eval (finalAssignment codec api rho) {linear(v['qr_root'])} = {native}.nativeQr api rho := by
    simp only [eval,Int.cast_one,one_mul,add_zero,{native}.final_qrRoot_value]
  rw [target,eval_append,eval_scale,{first_name}.first_g_value codec api rho one four linked,rootValue] at actual
  apply eq_sub_iff_add_eq.mpr
  simpa only [Int.cast_ofNat] using actual

theorem qr_product_value [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    eval (finalAssignment codec api rho) {linear(qr['target'])} =
      eval (finalAssignment codec api rho) {linear(qr['left'])} * eval (finalAssignment codec api rho) {linear(qr['right'])} := by
  rw [qr_output_value codec api rho one four linked]
  have scaled := Compiler.canonical_equal (finalAssignment codec api rho) {linear(qr['right'])}
    (scaleLinear (-4) {core}.firstG) (by decide)
  rw [scaled,eval_scale,{first_name}.first_g_value codec api rho one four linked]
  have choiceValue : eval (finalAssignment codec api rho) {linear(qr['left'])} =
      if {native}.nativeChoice api rho then 1 else 0 := by
    simp only [eval,Int.cast_one,one_mul,add_zero,{native}.final_choice_value]
  rw [choiceValue,({native}.computed_roots cardinality api rho).1]
  cases option : {native}.nativeChoice api rho <;>
    simp only [option,Bool.false_eq_true,if_true,if_false,Int.cast_neg,Int.cast_ofNat] <;> ring

theorem selected_target_value (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    eval (finalAssignment codec api rho) {linear(v['y_squared'])} =
      if {native}.nativeChoice api rho then {core}.nativeFirst rho else {core}.nativeTv rho * {core}.nativeFirst rho := by
  have actual := selected_product codec api rho one four linked
  have difference := Compiler.canonical_equal (finalAssignment codec api rho) {linear(result['products'][1]['right'])}
    (Compiler.subtract {core}.firstG {linear(v['gx2'])}) (by decide)
  rw [difference,Compiler.eval_subtract,{first_name}.first_g_value codec api rho one four linked,
    alternative_value codec api rho one four linked] at actual
  have choiceValue : eval (finalAssignment codec api rho) {linear(v['square'])} =
      if {native}.nativeChoice api rho then 1 else 0 := by
    simp only [eval,Int.cast_one,one_mul,add_zero,{native}.final_choice_value]
  rw [choiceValue] at actual
  have combined := Compiler.canonical_equal (finalAssignment codec api rho) {linear(v['y_squared'])}
    ({linear(v['gx2'])} ++ {linear(result['products'][1]['target'])}) (by decide)
  rw [combined,eval_append,alternative_value codec api rho one four linked,actual]
  cases option : {native}.nativeChoice api rho <;> simp only [option,Bool.false_eq_true,if_true,if_false] <;> ring

theorem expected_complete [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    Satisfies (finalAssignment codec api rho) expectedRows := by
  intro row member
  simp only [expectedRows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · have auxValue := aux_square codec api rho linked
    have input := Compiler.canonical_equal (finalAssignment codec api rho) {linear(aux['input'])}
      (Compiler.subtract {linear(qr['left'])} {linear(qr['right'])}) (by decide)
    rw [input,Compiler.eval_subtract] at auxValue
    change Square (eval (finalAssignment codec api rho) ({linear(qr['left'])} ++ {linear(qr['right'])}))
      (eval (finalAssignment codec api rho) ({linear(qr['certificate']['auxiliary'])} ++ scaleLinear 4 {linear(qr['target'])}))
    simp only [Square,eval_append,eval_scale,Int.cast_ofNat]
    rw [auxValue,qr_product_value cardinality codec api rho one four linked]
    ring
  · have rootValue : eval (finalAssignment codec api rho) {linear(v['y'])} = {native}.nativeY codec api rho := by
      simp only [eval,Int.cast_one,one_mul,add_zero,{native}.final_selectedRoot_value]
    change eval (finalAssignment codec api rho) {linear(v['y'])} * eval (finalAssignment codec api rho) {linear(v['y'])} =
      eval (finalAssignment codec api rho) {linear(v['y_squared'])}
    rw [rootValue,selected_target_value codec api rho one four linked]
    exact ({native}.selected_square_parity cardinality codec api rho).1

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
theorem complete_rows [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) : Satisfies (finalAssignment codec api rho) rawRows :=
  CompilerSignedCompletion.original_rows (finalAssignment codec api rho) expectedRows rawRows {copy}
    ({first_name}.final_link codec api rho linked) (expected_complete cardinality codec api rho one four linked) coverage
'''
    exports+=['alternative_value','qr_output_value','qr_product_value','selected_target_value','expected_complete',
              'coverage_checked','coverage','complete_rows']
    source+=''.join('#print axioms '+export+'\n' for export in exports)
    return name,_signature_audits(source+'end ShielddSecurity.'+name+'\n')
