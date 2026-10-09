"""Exact actual row composition to the independently constructed native image."""
from . import transfer_asset_map as maps,transfer_asset_map_completion as completion
from . import transfer_asset_map_native_rational_rows as rational,transfer_arithmetic as arithmetic
from . import transfer_relation as relation
from .transfer_balance_rows import combine


def plan(data,extracted,accepted_roles):
    inverse=rational.plan(data,extracted,accepted_roles);recipe=inverse['recipe'];checked=recipe['checked'];v=checked['values']
    products=[]
    def product(a,b,target=None):
        choices=[out for node,left,right,out in checked['nonlinear']
                 if ((a,b)==(left,right) or (b,a)==(left,right)) and (target is None or out==target)]
        if len(choices)!=1:raise relation.RelationError('native image unique actual product')
        out=choices[0];cert=arithmetic.product_certificate(a,b,out,recipe['normalized'])
        matches=[i for i,step in enumerate(recipe['steps']) if step['rows']==cert['rows']]
        if len(matches)!=1:raise relation.RelationError('native image exact materialized allocation')
        products.append(dict(certificate=cert,position=matches[0]));return out
    product(v['plus'],v['t'],v['den'])
    product(v['den'],v['inv'],checked['products'][1])
    product(v['den'],v['zero'],checked['products'][2])
    product(v['inv'],v['zero'],checked['products'][3])
    term=product(v['inv'],v['plus']);product(term,v['s'],checked['points'][0][0])
    term=product(v['inv'],v['t']);product(term,combine(v['s'],maps.ONE,-1),combine(checked['points'][0][1],v['zero'],-1))
    material=sorted({i for item in products for i in item['certificate']['rows']})
    chunks=sorted({item['position']//8 for item in products})
    if len(material)!=16 or len(chunks)>3:raise relation.RelationError('native image bounded sixteen original material rows')
    return dict(recipe=recipe,inverse=inverse,material=material,chunks=chunks,
                indices=sorted(set(material)|set(inverse['indices'])|{recipe['link_row']}))


def generate(data,extracted,accepted_roles):
    from .generate_hash_round import linear,_signature_audits
    result=plan(data,extracted,accepted_roles);recipe=result['recipe'];copy=recipe['checked']['metadata']['constant_copy']
    name='RuntimeTransferAssetMapNativeImageRows';native='RuntimeTransferAssetMapNativeSeeds'
    first='RuntimeTransferAssetMapNativeFirstRows';numeric='RuntimeTransferAssetMapNumericConstruction'
    rational_name='RuntimeTransferAssetMapNativeRationalRows';image='RuntimeTransferAssetMapRationalImage'
    chunks=['RuntimeTransferAssetMapMaterialization'+str(i) for i in result['chunks']];count=(len(recipe['steps'])+7)//8
    union=chunks[-1]+'.rawRows'
    for chunk in reversed(chunks[:-1]):union=chunk+'.rawRows ++ ('+union+')'
    source=f'''import ShielddSecurity.{rational_name}
import ShielddSecurity.{image}
'''+''.join('import ShielddSecurity.'+chunk+'\n' for chunk in chunks)+f'''set_option maxHeartbeats 250000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact actual metadata SHA256 {recipe['checked']['metadata_sha256']}.
-- Numeric material + derived total inverse + kept copy = actual native image.
abbrev modulus := {native}.modulus
def originalRowIndices : List Nat := {result['indices']}
def rawMaterialRows : List Row := [
'''+',\n'.join('⟨'+linear(recipe['raw'][i][0])+','+linear(recipe['raw'][i][1])+'⟩' for i in result['material'])+f''']
def sourceRawRows : List Row := {union}
def constantRow : Row := ⟨[(0,1),({copy},-1)],[]⟩
def supportRows : List Row := rawMaterialRows ++ ({rational_name}.rawRows ++ [constantRow])
variable {{F : Type}} [Field F] [CharP F modulus] [DecidableEq F]
abbrev finalAssignment (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) := {native}.completeAssignment codec api rho
theorem material_subset_checked : rawMaterialRows.all (fun row => decide (row ∈ sourceRawRows)) = true := by decide
theorem material_complete (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (linked : rho {copy} = rho 0) : Satisfies (finalAssignment codec api rho) rawMaterialRows := by
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
  exact sourceRows row (of_decide_eq_true (List.all_eq_true.mp material_subset_checked row member))

theorem coverage_checked : {image}.rawRows.all (fun row => decide (row ∈ supportRows)) = true := by decide
theorem coverage : ∀ row ∈ {image}.rawRows, row ∈ supportRows := by
  intro row member
  exact of_decide_eq_true (List.all_eq_true.mp coverage_checked row member)

theorem support_complete (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    Satisfies (finalAssignment codec api rho) supportRows := by
  intro row member
  simp only [supportRows,List.mem_append,List.mem_singleton] at member
  rcases member with material | inverse | rfl
  · exact material_complete codec api rho linked row material
  · exact {rational_name}.complete_rows codec api rho one four linked row inverse
  · have link := {first}.final_link codec api rho linked
    simp only [constantRow,eval,Int.cast_one,Int.cast_neg,one_mul,neg_one_mul,add_zero,Square,link]
    ring

theorem image_rows_complete (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    Satisfies (finalAssignment codec api rho) {image}.rawRows := by
  intro row member
  exact support_complete codec api rho one four linked row (coverage row member)

theorem native_image (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    {image}.actualImage (finalAssignment codec api rho) = {native}.nativeImage codec api rho := by
  have actual := {image}.rational_image (finalAssignment codec api rho)
    ({first}.final_one codec api rho one) four (image_rows_complete codec api rho one four linked)
  rw [{rational_name}.s_value codec api rho one four linked,{rational_name}.t_value] at actual
  exact actual

theorem native_image_curve [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    Group.OnCurve (RuntimeJubjub.d : F) ({image}.actualImage (finalAssignment codec api rho)) := by
  rw [native_image codec api rho one four linked]
  exact {native}.native_image_curve cardinality codec api rho
'''
    exports=['material_subset_checked','material_complete','coverage_checked','coverage','support_complete',
             'image_rows_complete','native_image','native_image_curve']
    source+=''.join('#print axioms '+export+'\n' for export in exports)
    return name,_signature_audits(source+'end ShielddSecurity.'+name+'\n')
