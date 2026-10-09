"""Actual final native first-coordinate/cubic and inverse assertion transport.

Only numeric chunk0 material rows are used as soundness inputs, and those are
derived from its constructive numeric program. The first inverse assertion is
a conclusion. No desired map output or desired square equation is assumed.
"""
from . import transfer_asset_map as maps,transfer_asset_map_first_cubic_completion as first
from . import transfer_relation as relation


def plan(data,extracted,accepted_roles):
    result=first.plan(data,extracted,accepted_roles);recipe=result['recipe']
    positions=[]
    for step in result['steps']:
        matches=[i for i,actual in enumerate(recipe['steps']) if actual==step]
        if len(matches)!=1:raise relation.RelationError('native first rows exact numeric constructor')
        positions.append(matches[0])
    indices=sorted({i for step in result['steps'] for i in step['rows']})
    assertion=set(result['indices'])-set(indices)-{recipe['link_row']}
    if len(indices)!=8 or len(assertion)!=1:
        raise relation.RelationError('native first exact eight material/one assertion rows')
    chunks=sorted({position//8 for position in positions})
    if len(chunks)>3:raise relation.RelationError('native first material chunk bound')
    return dict(first=result,material=indices,assertion=assertion.pop(),chunks=chunks)


def generate(data,extracted,accepted_roles):
    from . import transfer_asset_map_materialization_sequence as numeric_plan
    return _from_checked(plan(data,extracted,accepted_roles),
        numeric_plan.plan(data,extracted,accepted_roles)['seed_floor'])


def _from_checked(result,floor):
    """Render an already validated bounded material layout; no ingress bypass."""
    from .generate_hash_round import linear,signed,_signature_audits
    core=result['first'];recipe=core['recipe']
    copy=recipe['checked']['metadata']['constant_copy'];q=core['q'];root=recipe['seeds']['selectedRoot'];start=recipe['seeds']['bit0']
    name='RuntimeTransferAssetMapNativeFirstRows';native='RuntimeTransferAssetMapNativeSeeds'
    first_name='RuntimeTransferAssetMapFirstCubicConstruction';numeric='RuntimeTransferAssetMapNumericConstruction'
    chunks=['RuntimeTransferAssetMapMaterialization'+str(i) for i in result['chunks']]
    target=core['quotient']['output'];actual=recipe['raw'][result['assertion']]
    source=f'''import ShielddSecurity.{native}
'''+''.join('import ShielddSecurity.'+chunk+'\n' for chunk in chunks)+f'''
import ShielddSecurity.CompilerSignedCompletion
set_option maxHeartbeats 350000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact actual metadata SHA256 {recipe['checked']['metadata_sha256']}.
-- First inverse assertion derives computed native cancellation, not earlier satisfaction.
abbrev modulus := {native}.modulus
def originalMaterialRowIndices : List Nat := {result['material']}
def originalAssertionRow : Nat := {result['assertion']}
def rawMaterialRows : List Row := [
'''+',\n'.join('⟨'+linear(recipe['raw'][i][0])+','+linear(recipe['raw'][i][1])+'⟩' for i in result['material'])+f''']
def materialRows : List Row := Compiler.unoutlineRows {copy} rawMaterialRows
def sourceRawRows : List Row := {' ++ '.join(chunk+'.rawRows' for chunk in chunks)}
def rawRows : List Row := [⟨{linear(actual[0])},{linear(actual[1])}⟩]
def expectedRows : List Row := [⟨Compiler.subtract {linear(target)} [(0,1)],[]⟩]
variable {{F : Type}} [Field F] [CharP F modulus] [DecidableEq F]
abbrev finalAssignment (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) := {native}.completeAssignment codec api rho

theorem material_subset_checked : rawMaterialRows.all (fun row => decide (row ∈ sourceRawRows)) = true := by decide
theorem material_subset : ∀ row ∈ rawMaterialRows, row ∈ sourceRawRows := by
  intro row member
  exact of_decide_eq_true (List.all_eq_true.mp material_subset_checked row member)

theorem final_one (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (one : rho 0 = 1) : finalAssignment codec api rho 0 = 1 := by
  unfold finalAssignment {native}.completeAssignment
  rw [{numeric}.preserves _ 0 (by decide),{native}.preserves codec api rho 0 (by decide) (by decide) (by decide),one]

theorem final_link (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (linked : rho {copy} = rho 0) :
    finalAssignment codec api rho {copy} = finalAssignment codec api rho 0 := by
  unfold finalAssignment {native}.completeAssignment
  rw [{numeric}.preserves _ {copy} (by decide),{numeric}.preserves _ 0 (by decide),
    {native}.preserves codec api rho {copy} (by decide) (by decide) (by decide),
    {native}.preserves codec api rho 0 (by decide) (by decide) (by decide),linked]

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
    source+=f'''  have raw : Satisfies (finalAssignment codec api rho) rawMaterialRows := by
    intro row member
    exact sourceRows row (material_subset row member)
  intro row member
  obtain ⟨actual,present,rfl⟩ := List.mem_map.mp member
  simpa only [Compiler.eval_unoutline _ {copy} _ (final_link codec api rho linked)] using raw actual present

theorem input_value (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) : eval (finalAssignment codec api rho) {first_name}.input = {first_name}.nativeInput rho := by
  change eval (finalAssignment codec api rho) {first_name}.input = eval rho {first_name}.input
  apply eval_agrees
  intro term member
  have checks : {first_name}.input.all (fun term => decide (
      term.1 < {floor} ∧ term.1 ∉ {native}.otherWrites ∧ term.1 ≠ {root} ∧
      (term.1 < {start} ∨ {start}+255 ≤ term.1))) = true := by decide
  have outside := of_decide_eq_true (List.all_eq_true.mp checks term member)
  unfold finalAssignment {native}.completeAssignment
  rw [{numeric}.preserves _ term.1 (CompilerSequenceCompletion.frame_column {copy} {floor} []
    (PoseidonCompletion.writes {numeric}.steps) term.1 {numeric}.writes_checked ⟨Or.inr outside.1,by simp⟩)]
  exact {native}.preserves codec api rho term.1 outside.2.1 outside.2.2.1 outside.2.2.2
'''
    exports=['material_subset_checked','material_subset','final_one','final_link','material_complete','input_value']
    for product in core['products']:
        cert=product['certificate'];a,b=product['left'],product['right'];left,right=(b,a) if cert.get('swapped') else (a,b)
        source+=f'''theorem {product['label']}_product (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    eval (finalAssignment codec api rho) {linear(product['target'])} =
      eval (finalAssignment codec api rho) {linear(a)} * eval (finalAssignment codec api rho) {linear(b)} := by
  have actual := ScalarRows.checked_product_sound (finalAssignment codec api rho)
    (final_one codec api rho one) four materialRows (material_complete codec api rho linked)
    {linear(left)} {linear(right)} {linear(product['target'])} (.product {linear(cert['auxiliary'])}) (by decide)
  simpa only [mul_comm] using actual
'''
        exports.append(product['label']+'_product')
    source+=f'''theorem tv_value (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    eval (finalAssignment codec api rho) {first_name}.tv = {first_name}.nativeTv rho := by
  have actual := tv_product codec api rho one four linked
  have scaled := Compiler.canonical_equal (finalAssignment codec api rho) {linear(core['products'][0]['left'])}
    (scaleLinear 5 {first_name}.input) (by decide)
  rw [scaled,eval_scale,input_value] at actual
  have inputRight := Compiler.canonical_equal (finalAssignment codec api rho)
    {linear(core['products'][0]['right'])} {first_name}.input (by decide)
  rw [inputRight,input_value] at actual
  simpa only [{first_name}.tv,{first_name}.nativeTv,Int.cast_ofNat,Nat.cast_ofNat] using actual

theorem first_x_value (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) : eval (finalAssignment codec api rho) {first_name}.firstX = {first_name}.nativeX rho := by
  have actual := Compiler.canonical_equal (finalAssignment codec api rho) {first_name}.firstX
    (scaleLinear (-RuntimeElligatorAlgebra.c1) [({q},1)]) (by decide)
  simpa only [eval_scale,eval,Int.cast_neg,Int.cast_one,one_mul,add_zero,
    {native}.final_firstInverse_value,{first_name}.nativeX] using actual

theorem first_g_value (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    eval (finalAssignment codec api rho) {first_name}.firstG = {first_name}.nativeFirst rho := by
  have first := first_product codec api rho one four linked
  have second := cubic_product codec api rho one four linked
  have c1Value : eval (finalAssignment codec api rho) [(0,RuntimeElligatorAlgebra.c1)] =
      (RuntimeElligatorAlgebra.c1 : F) := by simp only [eval,final_one codec api rho one,mul_one,add_zero]
  have c2Value : eval (finalAssignment codec api rho) [(0,RuntimeElligatorAlgebra.c2)] =
      (RuntimeElligatorAlgebra.c2 : F) := by simp only [eval,final_one codec api rho one,mul_one,add_zero]
  have firstAdd := Compiler.canonical_equal (finalAssignment codec api rho) {linear(core['products'][1]['left'])}
    ({first_name}.firstX ++ [(0,RuntimeElligatorAlgebra.c1)]) (by decide)
  have secondAdd := Compiler.canonical_equal (finalAssignment codec api rho) {linear(core['products'][2]['left'])}
    ({linear(core['products'][1]['target'])} ++ [(0,RuntimeElligatorAlgebra.c2)]) (by decide)
  rw [eval_append,c1Value] at firstAdd
  rw [eval_append,c2Value] at secondAdd
  rw [firstAdd] at first
  rw [secondAdd,first,first_x_value] at second
  change eval (finalAssignment codec api rho) {first_name}.firstG =
    (({first_name}.nativeX rho + (RuntimeElligatorAlgebra.c1 : F)) *
      eval (finalAssignment codec api rho) {first_name}.firstX +
      (RuntimeElligatorAlgebra.c2 : F)) *
      eval (finalAssignment codec api rho) {first_name}.firstX at second
  rw [first_x_value] at second
  exact second

theorem denominator_value (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    eval (finalAssignment codec api rho) {first_name}.denominator = 1 + {first_name}.nativeTv rho := by
  have actual := Compiler.canonical_equal (finalAssignment codec api rho) {first_name}.denominator
    ([(0,1)] ++ {first_name}.tv) (by decide)
  simpa only [eval_append,eval,final_one codec api rho one,Int.cast_one,one_mul,add_zero,
    tv_value codec api rho one four linked] using actual

theorem inverse_target_value [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    eval (finalAssignment codec api rho) {first_name}.inverseTarget = 1 := by
  have actual := inverseProduct_product codec api rho one four linked
  change eval (finalAssignment codec api rho) {first_name}.inverseTarget =
    eval (finalAssignment codec api rho) [({q},1)] * eval (finalAssignment codec api rho) {first_name}.denominator at actual
  have qValue : eval (finalAssignment codec api rho) [({q},1)] = {first_name}.nativeInverse rho := by
    simp only [eval,Int.cast_one,one_mul,add_zero,{native}.final_firstInverse_value]
  rw [qValue,denominator_value codec api rho one four linked] at actual
  exact actual.trans (inv_mul_cancel₀ ({first_name}.native_denominator_nonzero cardinality rho))

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
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    Satisfies (finalAssignment codec api rho) rawRows := by
  have expected : Satisfies (finalAssignment codec api rho) expectedRows := by
    intro row member
    simp only [expectedRows,List.mem_singleton] at member
    subst row
    have value : eval (finalAssignment codec api rho) {linear(target)} = 1 :=
      inverse_target_value cardinality codec api rho one four linked
    have constant : eval (finalAssignment codec api rho) [(0,1)] = 1 := by
      simp only [eval,Int.cast_one,one_mul,add_zero,final_one codec api rho one]
    rw [Compiler.eval_subtract,value,constant]
    simp only [eval,sub_self,Square,zero_mul]
  exact CompilerSignedCompletion.original_rows (finalAssignment codec api rho) expectedRows rawRows {copy}
    (final_link codec api rho linked) expected coverage
'''
    exports+=['tv_value','first_x_value','first_g_value','denominator_value','inverse_target_value',
              'coverage_checked','coverage','complete_rows']
    source+=''.join('#print axioms '+export+'\n' for export in exports)
    return name,_signature_audits(source+'end ShielddSecurity.'+name+'\n')
