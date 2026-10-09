"""Current bounded AK cone and subgroup composition candidates, not publication."""
import hashlib
import copy
from . import transfer_ak_subgroup as ak
from .generate_hash_round import linear
from .generate_group_cones import generate_checked


def cofactor_only_extraction(data, checked, ivk, digest):
    """Remove only the final x-inverse pair/assertion, retaining the cofactor rows."""
    state=ak.inspect_metadata(data,digest,ivk)
    role='node.'+str(state['nonidentity_product'][1])
    pairs=[p for p in checked['products'] if p['role'] == role]
    assertions=[t for t in checked['templates'] if t['roles'] == ['inverse-assert.3']]
    if len(pairs) != 1 or len(assertions) != 1 or len(pairs[0]['rows']) != 2:
        raise ak.relation.RelationError('missing unique cofactor-only inverse cut')
    removed=set(pairs[0]['rows']+[assertions[0]['row']])
    result=copy.deepcopy(checked)
    result['selected_rows']=[r for r in result['selected_rows'] if r['row'] not in removed]
    result['products']=[p for p in result['products'] if p['role'] != role]
    result['templates']=[t for t in result['templates'] if t not in assertions]
    if len(removed) != 3 or len(result['selected_rows']) != 71:
        raise ak.relation.RelationError('wrong cofactor-only row count')
    result['scope']='actual cofactor-only rows; identity allowed; source-role/completion joins open'
    return result


def generate_cones(data, checked, ivk, digest, *, cofactor_only=False):
    if cofactor_only:
        checked=cofactor_only_extraction(data,checked,ivk,digest)
    selected = ak.cone_certificates(data,checked,ivk,digest)
    namespace='RuntimeTransferCofactorCones' if cofactor_only else 'RuntimeTransferAkCones'
    return generate_checked(selected,hashlib.sha256(data).hexdigest(),digest,namespace,True)


def generate_composition(data, checked, ivk, digest, *, cofactor_only=False):
    if cofactor_only:
        checked=cofactor_only_extraction(data,checked,ivk,digest)
    state = ak.inspect_metadata(data,digest,ivk)
    selected = ak.cone_certificates(data,checked,ivk,digest)
    formulas = ak.match_formulas(state)
    roles = {'point_x':state['inputs'][0],'point_y':state['inputs'][1],
             'preimage_x':state['inputs'][2],'preimage_y':state['inputs'][3],
             'point_inverse':state['nonidentity'][1]}
    for i,double in enumerate(state['doubles']):
        roles.update({f'double{i}_x':double[2],f'double{i}_y':double[3],
                      f'inverse{i}':formulas['inverse_witnesses'][i]})
    def lc(handle): return linear(state['derived'][handle])
    def cone_output(i): return formulas['cones'][i]['output']
    def cone_defs(index):
        cone = selected['cones'][index]
        prefix = cone['role'].replace('.','_')
        return ', '.join('C.'+prefix+'_'+identity for identity in cone['inputs']+[cone['output']])
    rows = {row['row']:row for row in checked['selected_rows']}
    products = {p['role']:p['rows'] for p in checked['products']}
    copy = state['metadata']['constant_copy']
    def inverse_equation(index,node):
        multiply,left,right = state['nodes'][node]
        if not multiply: raise ValueError('inverse product must multiply')
        pair = products['node.'+str(node[1])]
        aux = linear(ak.canonical((0 if c == copy else c,int(v,16)) for c,v in rows[pair[0]]['b']))
        return f'''  have product{index} := Compiler.checked_product_sound rho C.rows
    ({lc(left)}) ({lc(right)}) ({lc(node)}) ({aux})
    (C.fourNonzero (F := F)) normalized (by decide) (by decide)
  have assertion{index} := ScalarComparisonBounds.checked_equality rho C.rows normalized
    ({lc(node)}) [(0,1)] (by decide)
  have inverseEquation{index} : eval rho ({lc(left)}) * eval rho ({lc(right)}) = 1 := by
    rw [product{index}] at assertion{index}
    simpa [eval, one] using assertion{index}
'''
    out = [f'''import ShielddSecurity.RuntimeTransferAkCones
import ShielddSecurity.TransferSubgroup
import ShielddSecurity.ScalarComparisonBounds
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeTransferAk
-- Metadata SHA256: {hashlib.sha256(data).hexdigest()}
-- Full relation extraction digest: {digest}
-- Selected original rows: {sorted(rows)}
def rawRows : List Row := C.rawRows
def subgroupOrder : Nat := 6554484396890773809930967563523245729705921265872317281365359162392183254199
''']
    for role,handle in roles.items(): out.append(f'def {role} : Linear := {lc(handle)}\n')
    for point,x,y in [('point','point_x','point_y'),('preimage','preimage_x','preimage_y'),
                      ('twice','double0_x','double0_y'),('four','double1_x','double1_y'),('eight','double2_x','double2_y')]:
        out.append(f'def {point} {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F := ⟨eval rho {x},eval rho {y}⟩\n')
    out.append('''
theorem actual_ak_subgroup {F J : Type} [Field F] [CharP F C.modulus] [AddCommGroup J]
    (model : Group.StandardCurveModel J (C.coefficientD : F))
    (standardOrder : ∀ represented : J, (8 * subgroupOrder) • represented = 0)
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    ∃ represented : J, model.coordinates represented = point rho ∧
      subgroupOrder • represented = 0 ∧ represented ≠ 0 := by
  have normalized : Satisfies rho C.rows :=
    Compiler.unoutline_rows_sound rho '''+str(copy)+''' C.rawRows satisfied C.constantLink
  have left := C.curve_left_sound rho one satisfied
  have right := C.curve_right_sound rho one satisfied
''')
    out.append(f'  dsimp only [{cone_defs(0)}] at left\n  dsimp only [{cone_defs(1)}] at right\n')
    out.append(f'''  have curve := ScalarComparisonBounds.checked_equality rho C.rows normalized
    ({lc(state['curve'][0])}) ({lc(state['curve'][1])}) (by decide)
  have valid : Group.OnCurve (C.coefficientD : F) (preimage rho) := by
    rw [left,right] at curve
    exact curve
''')
    for i,node in enumerate(formulas['inverse_assert_products']):
        before,after = [('preimage','twice'),('twice','four'),('four','eight')][i]
        out.append(inverse_equation(i,node))
        denominator = cone_output(2+3*i)
        out.append(f'''  have denominator{i} := C.double{i}_denominator_sound rho one satisfied
  dsimp only [{cone_defs(2+3*i)}] at denominator{i}
  have denominatorInverse{i} :
      ((1 + Group.delta (C.coefficientD : F) ({before} rho) ({before} rho)) *
       (1 - Group.delta (C.coefficientD : F) ({before} rho) ({before} rho))) *
       eval rho inverse{i} = 1 := by
    dsimp only [{before}, {('preimage_x, preimage_y' if i == 0 else f'double{i-1}_x, double{i-1}_y')}, inverse{i}]
    rw [← denominator{i}]
    simpa only [inverse{i}, mul_comm] using inverseEquation{i}
  have x{i} := C.double{i}_after_x_sound rho one satisfied
  have y{i} := C.double{i}_after_y_sound rho one satisfied
  dsimp only [{cone_defs(3+3*i)}] at x{i}
  dsimp only [{cone_defs(4+3*i)}] at y{i}
  have step{i} : {after} rho = Group.affineAdd (C.coefficientD : F) ({before} rho) ({before} rho) :=
    TransferSubgroup.shared_inverse_affine (C.coefficientD : F) (eval rho inverse{i})
      ({before} rho) ({before} rho) ({after} rho) denominatorInverse{i} x{i} y{i}
''')
    for axis in ('x','y'):
        k = 0 if axis == 'x' else 1
        out.append(f'''  have endpoint{axis} := ScalarComparisonBounds.checked_equality rho C.rows normalized
    ({lc(state['inputs'][k])}) ({lc(state['doubles'][-1][k+2])}) (by decide)
''')
    out.append('''  have binding : point rho = eight rho := by
    exact congrArg₂ Group.Point.mk endpointx endpointy
''')
    if cofactor_only:
        out.append('''  obtain ⟨represented,coordinates,subgroup⟩ :=
    Group.cofactor_image_annihilated (C.coefficientD : F) model subgroupOrder
      standardOrder (preimage rho) (twice rho) (four rho) (eight rho)
      valid step0 step1 step2
  exact ⟨represented,coordinates.trans binding.symm,subgroup⟩
''')
    else:
        out.append(inverse_equation(3,state['nonidentity_product']))
        out.append('''  exact TransferSubgroup.cofactor_nonidentity (C.coefficientD : F) model subgroupOrder
    standardOrder (preimage rho) (twice rho) (four rho) (eight rho) (point rho)
    valid step0 step1 step2 binding (eval rho point_inverse) inverseEquation3
''')
    out.append('''
set_option pp.all true in
#check @actual_ak_subgroup
#print axioms actual_ak_subgroup
end ShielddSecurity.RuntimeTransferAk
''')
    source=''.join(out).replace('C.', 'ShielddSecurity.RuntimeTransferAkCones.')
    if cofactor_only:
        source=source.replace('RuntimeTransferAkCones','RuntimeTransferCofactorCones').replace('RuntimeTransferAk','RuntimeTransferCofactor')
        source=source.replace('actual_ak_subgroup','actual_cofactor_subgroup')
        source=source.replace('subgroupOrder • represented = 0 ∧ represented ≠ 0','subgroupOrder • represented = 0')
    return source


def generate_projection_join():
    return '''import ShielddSecurity.RuntimeTransferAk
import ShielddSecurity.RuntimeTransferAuthorization
set_option maxHeartbeats 500000
namespace ShielddSecurity.RuntimeTransferAuthorizationAk

def originalRows : List Row := RuntimeTransferIvk.originalRows ++ RuntimeTransferAk.rawRows
def decodePoint {F : Type} [Field F] (codec : TransferReduction.CanonicalField F)
    (point : Group.Point F) : TransferCore.Affine := ⟨codec.decode point.x,codec.decode point.y⟩

theorem point_columns : RuntimeTransferAk.point_x = [(1980,1)] ∧
    RuntimeTransferAk.point_y = [(1981,1)] := by decide

theorem decoded_nonidentity {F J : Type} [Field F] [AddCommGroup J]
    (codec : TransferReduction.CanonicalField F) (d : F)
    (model : Group.StandardCurveModel J d) (represented : J) (nonzero : represented ≠ 0) :
    TransferSem.nonidentity (decodePoint codec (model.coordinates represented)) := by
  intro same
  have hx := congrArg (fun point : TransferCore.Affine => (point.x : F)) same
  have hy := congrArg (fun point : TransferCore.Affine => (point.y : F)) same
  have x : (model.coordinates represented).x = 0 := by
    simpa only [decodePoint, codec.roundtrip, Nat.cast_zero] using hx
  have y : (model.coordinates represented).y = 1 := by
    simpa only [decodePoint, codec.roundtrip, Nat.cast_one] using hy
  have fields : model.coordinates represented = Group.identityPoint := by
    have eta : ∀ point : Group.Point F, point = ⟨point.x,point.y⟩ := by
      intro point; cases point; rfl
    calc
      model.coordinates represented = ⟨(model.coordinates represented).x,(model.coordinates represented).y⟩ := eta _
      _ = Group.identityPoint := congrArg₂ Group.Point.mk x y
  exact nonzero (model.injective (fields.trans model.identity.symm))

/-- Same assignment and same scalar witness projection; the subgroup interpreter
is an explicit decoded-point operation contract, not an upstream security claim.
Other authorization conjuncts and full source qualification remain open. -/
theorem projected_authorization_ak {F J : Type} [Field F]
    [CharP F RuntimeTransferIvk.p] [AddCommGroup J]
    (codec : TransferReduction.CanonicalField F) (c : TransferSem.Crypto)
    (base : TransferSem.Witness) (rho : Nat → F)
    (model : Group.StandardCurveModel J (RuntimeTransferAkCones.coefficientD : F))
    (standardOrder : ∀ represented : J, (8 * RuntimeTransferAk.subgroupOrder) • represented = 0)
    (subgroupInterpreter : ∀ represented : J, RuntimeTransferAk.subgroupOrder • represented = 0 →
      c.subgroup (decodePoint codec (model.coordinates represented)))
    (hashInterpreter : ∀ nk ax ay : Nat,
      nk < Scalar.modulus → ax < Scalar.modulus → ay < Scalar.modulus →
      c.hash .incomingViewingKey [nk,ax,ay] = codec.decode
        (Poseidon.hash6 (Poseidon.castParameters RuntimeHashBlock_authorization_ivk_0.parameters) 16
          [(nk : F),(ax : F),(ay : F)]))
    (one : rho 0 = 1) (satisfied : Satisfies rho originalRows) :
    let w := RuntimeTransferAuthorization.scalar_projection codec rho base
    TransferSem.AuthorizationScalarSem c w ∧ TransferSem.ValidPoint c w.auth.ak ∧
      TransferSem.nonidentity w.auth.ak := by
  have ivkSatisfied : Satisfies rho RuntimeTransferIvk.originalRows := by
    intro row member; exact satisfied row (List.mem_append.mpr (Or.inl member))
  have akSatisfied : Satisfies rho RuntimeTransferAk.rawRows := by
    intro row member; exact satisfied row (List.mem_append.mpr (Or.inr member))
  have numeric := RuntimeTransferAuthorization.projected_authorization_scalar codec c base rho
    one (RuntimeTransferAkCones.fourNonzero (F := F)) ivkSatisfied hashInterpreter
  obtain ⟨represented,coordinates,annihilated,nonzero⟩ := RuntimeTransferAk.actual_ak_subgroup
    model standardOrder rho one akSatisfied
  have role : (RuntimeTransferAuthorization.scalar_projection codec rho base).auth.ak =
      decodePoint codec (model.coordinates represented) := by
    rw [coordinates]
    simp only [RuntimeTransferAuthorization.scalar_projection,decodePoint,RuntimeTransferAk.point,
      point_columns.1,point_columns.2,eval,Int.cast_one,one_mul,add_zero]
  have canonical := (RuntimeTransferAuthorization.projected_raw_fields_canonical codec rho base).1
  refine ⟨numeric, ⟨canonical, ?_⟩, ?_⟩
  · rw [role]; exact subgroupInterpreter represented annihilated
  · rw [role]; exact decoded_nonidentity codec _ model represented nonzero

set_option pp.all true in
#check @point_columns
#print axioms point_columns
set_option pp.all true in
#check @decoded_nonidentity
#print axioms decoded_nonidentity
set_option pp.all true in
#check @projected_authorization_ak
#print axioms projected_authorization_ak
end ShielddSecurity.RuntimeTransferAuthorizationAk
'''
