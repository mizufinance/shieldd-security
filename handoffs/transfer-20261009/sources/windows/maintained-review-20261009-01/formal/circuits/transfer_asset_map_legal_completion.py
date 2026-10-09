"""Original map870 plus inverse3 under the independent native success guard.

This local constructor starts at the captured map input u. Its lawful guard
executes the pure native map at u before native balance multiplication. Binding
u to ASSET_GENERATOR(domain26, original asset) is a separate actual hash join;
this module does not claim that source-level Transfer admission is instantiated.
"""
from . import transfer_asset_map_inverse_frame as frame
from . import transfer_asset_map_native_double_rows as doubles
from . import transfer_relation as relation


def plan(data, extracted, inverse_data, inverse_extracted, accepted_roles):
    result = frame.plan(data, extracted, inverse_data, inverse_extracted, accepted_roles)
    point = doubles.plan(data, extracted, accepted_roles, 2)['point']
    if result['inverse']['denominator'] != point['output'][0]:
        raise relation.RelationError('legal map exact final native x/inverse denominator LC')
    if len(result['map']['recipe']['raw']) != 870 or len(result['inverse']['raw']) != 3:
        raise relation.RelationError('legal map exact870 plus independent inverse3 rows')
    return result


def generate(data, extracted, inverse_data, inverse_extracted, accepted_roles):
    from .generate_hash_round import _signature_audits
    result = plan(data, extracted, inverse_data, inverse_extracted, accepted_roles)
    name = 'RuntimeTransferAssetMapLegalCompletion'
    core = 'RuntimeTransferAssetMapFirstCubicConstruction'
    seeds = 'RuntimeTransferAssetMapNativeSeeds'
    source_map = 'RuntimeTransferAssetMapNativeSource'
    complete = 'RuntimeTransferAssetMapNativeCompletion'
    inverse = 'RuntimeTransferAssetGeneratorInverseCompletion'
    framing = 'RuntimeTransferAssetMapInverseFrame'
    copy = result['copy']
    source = f'''import ShielddSecurity.{source_map}
import ShielddSecurity.{framing}
import ShielddSecurity.NativeTransferAdmission
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Exact map and inverse share qualified parent {result['inverse']['checked']['metadata_sha256']}.
-- Independent balanceNative success excludes identity after pure mapping.
-- Actual domain26 asset/hash input and SDK ABI joins are separate prerequisites.
abbrev modulus := {complete}.modulus
variable {{F : Type}} [Field F] [CharP F modulus] [DecidableEq F]
def nativeGenerator (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (u : F) : Group.Point F :=
  ElligatorNativeProgram.generatorValue codec api (RuntimeElligatorAlgebra.c1 : F)
    (RuntimeElligatorAlgebra.c2 : F) (RuntimeElligatorAlgebra.k : F) (RuntimeJubjub.d : F) u
abbrev completeAssignment (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) := {framing}.completeAssignment codec api rho
def rawRows : List Row := {complete}.rawRows ++ {inverse}.rawRows

theorem native_generator_value [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) :
    nativeGenerator codec api ({core}.nativeInput rho) = {seeds}.nativePoint3 codec api rho := by
  have direct := ElligatorNativeProgram.source_defined codec api ({seeds}.field_odd (F := F))
    ({seeds}.five_nonzero (F := F)) ({seeds}.five_euler cardinality)
    (RuntimeElligatorAlgebra.c1 : F) (RuntimeElligatorAlgebra.c2 : F)
    (RuntimeElligatorAlgebra.k : F) (RuntimeJubjub.d : F) ({core}.nativeInput rho)
  exact Option.some.inj (direct.symm.trans ({source_map}.native_program cardinality codec api rho))

theorem native_generator_x [Fintype F] (cardinality : Fintype.card F = modulus)
    {{J : Type}} [AddCommGroup J] (model : Group.StandardCurveModel J (RuntimeJubjub.d : F))
    (fullOrder : ∀ point : J, (8 * Scalar.order) • point = 0)
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (blindingGenerator : Group.Point F) (inputs outputs : NativeTransferAdmission.Amounts)
    (blinding : F) (balance : Group.Point F)
    (accepted : NativeTransferAdmission.balanceNative codec writer (RuntimeJubjub.d : F)
      (nativeGenerator codec api) blindingGenerator ({core}.nativeInput rho)
      inputs outputs blinding = .ok balance) :
    ({seeds}.nativePoint3 codec api rho).x ≠ 0 := by
  have admitted := NativeTransferAdmission.balance_success_nonidentity codec writer (RuntimeJubjub.d : F)
    (nativeGenerator codec api) blindingGenerator ({core}.nativeInput rho) inputs outputs blinding balance accepted
  rw [native_generator_value cardinality codec api rho] at admitted
  obtain ⟨point,represented⟩ := model.covers ({seeds}.nativeImage codec api rho)
    ({seeds}.native_image_curve cardinality codec api rho)
  have coordinates : {seeds}.nativePoint3 codec api rho = model.coordinates (8 • point) := by
    rw [{source_map}.native_eight codec api rho,← represented]
    exact GroupNativeCofactor.native_eight_coordinates (RuntimeJubjub.d : F) (RuntimeJubjub.imaginary : F)
      model (RuntimeJubjub.nonsquare cardinality) RuntimeJubjub.imaginary_square point
  have subgroup : Scalar.order • (8 • point) = 0 := by
    rw [← mul_nsmul,Nat.mul_comm]
    exact fullOrder point
  rw [coordinates]
  apply GroupNativeNonidentity.subgroup_nonidentity_x (RuntimeJubjub.d : F) model (8 • point) subgroup
  intro zero
  apply admitted
  rw [coordinates,zero,model.identity]

theorem generator_x_value [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    eval ({complete}.completeAssignment codec api rho) {inverse}.generatorX =
      ({seeds}.nativePoint3 codec api rho).x := by
  have coordinate := congrArg Group.Point.x ({complete}.native_cofactor cardinality codec api rho one four linked)
  exact coordinate

theorem map_linked (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) (linked : rho {copy} = rho 0) :
    {complete}.completeAssignment codec api rho {copy} = {complete}.completeAssignment codec api rho 0 := by
  rw [{complete}.preserves codec api rho {copy} (by decide) (by decide) (by decide) (by decide),
    {complete}.preserves codec api rho 0 (by decide) (by decide) (by decide) (by decide),linked]

theorem complete_rows [Fintype F] (cardinality : Fintype.card F = modulus)
    {{J : Type}} [AddCommGroup J] (model : Group.StandardCurveModel J (RuntimeJubjub.d : F))
    (fullOrder : ∀ point : J, (8 * Scalar.order) • point = 0)
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0)
    (blindingGenerator : Group.Point F) (inputs outputs : NativeTransferAdmission.Amounts)
    (blinding : F) (balance : Group.Point F)
    (accepted : NativeTransferAdmission.balanceNative codec writer (RuntimeJubjub.d : F)
      (nativeGenerator codec api) blindingGenerator ({core}.nativeInput rho)
      inputs outputs blinding = .ok balance) :
    Satisfies (completeAssignment codec api rho) rawRows := by
  have nonzero := native_generator_x cardinality model fullOrder codec writer api rho
    blindingGenerator inputs outputs blinding balance accepted
  have legal : eval ({complete}.completeAssignment codec api rho) {inverse}.generatorX ≠ 0 := by
    rw [generator_x_value cardinality codec api rho one four linked]
    exact nonzero
  have inverseRows := {inverse}.complete_rows ({complete}.completeAssignment codec api rho)
    (map_linked codec api rho linked) legal
  intro row member
  rcases List.mem_append.mp member with mapRow | inverseRow
  · exact {framing}.map_rows_complete cardinality codec api rho one four linked row mapRow
  · exact inverseRows row inverseRow
'''
    exports = ['native_generator_value', 'native_generator_x', 'generator_x_value', 'map_linked', 'complete_rows']
    source += ''.join('#print axioms ' + export + '\n' for export in exports)
    return name, _signature_audits(source + 'end ShielddSecurity.' + name + '\n')
