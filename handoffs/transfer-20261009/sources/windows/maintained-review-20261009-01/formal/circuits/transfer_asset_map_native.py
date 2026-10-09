"""Actual canonical encoding/QR/rational-image bridge to native root contracts.

The pinned sqrt API and canonical byte parity contracts are explicit. These
contracts describe native intermediate values, never equality to a circuit
witness or a native final map result. Cofactor/source-u composition is separate.
"""
from . import transfer_asset_map as maps
from . import transfer_asset_map_choice as choice, transfer_asset_map_image as image


def generate(data, extracted, accepted_roles):
    from .generate_hash_round import linear, _signature_audits
    checked = maps.certificates(data, extracted, accepted_roles)['checked']
    choice_name, _ = choice.generate(data, extracted, accepted_roles)
    image_name, _ = image.generate(data, extracted, accepted_roles)
    encoding_name = 'RuntimeTransferAssetMapEncoding'
    name = 'RuntimeTransferAssetMapNativeRoot'
    dependencies = [choice_name, encoding_name, image_name]
    source = ''.join('import ShielddSecurity.' + dependency + '\n' for dependency in dependencies)
    source += f'''import ShielddSecurity.ElligatorNative
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Original metadata SHA256 {checked['metadata_sha256']}.
-- Native root/codec contracts are explicit; native source-u/cofactor joins remain open.
def rawRows : List Row := ''' + ' ++ '.join(d + '.rawRows' for d in dependencies) + '\n'
    exports = []
    for offset, dependency in enumerate(dependencies):
        export = 'included' + str(offset)
        source += f'''theorem {export} : ∀ row ∈ {dependency}.rawRows, row ∈ rawRows := by
  intro row member
  simp only [rawRows,List.mem_append]
  tauto
'''
        exports.append(export)

    def satisfies(offset):
        return f'(fun row member => satisfied row (included{offset} row member))'

    source += f'''noncomputable def nativeSelectedX {{F : Type}} [Field F]
    (rho : Nat → F) (nativeOption : Bool) : F :=
  if nativeOption then eval rho {choice_name}.x1 else eval rho {choice_name}.x2

theorem actual_parity {{F : Type}} [Field F] [CharP F {choice_name}.modulus]
    (codec : TransferReduction.CanonicalField F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    codec.decode (eval rho {choice_name}.y) % 2 =
      if {choice_name}.choice rho then 1 else 0 := by
  exact {encoding_name}.actual_parity codec rho one four {satisfies(1)}

theorem native_root_unique {{F : Type}} [Field F] [CharP F {choice_name}.modulus] [Fintype F]
    (codec : TransferReduction.CanonicalField F) (cardinality : Fintype.card F = {choice_name}.modulus)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) (nativeOption : Bool) (nativeY : F)
    (sqrtSpecification : nativeOption = true ↔ ∃ root : F, root * root = eval rho {choice_name}.gx1)
    (nativeSquare : nativeY * nativeY =
      if nativeOption then eval rho {choice_name}.gx1 else eval rho {choice_name}.gx2)
    (nativeParity : codec.decode nativeY % 2 = if nativeOption then 1 else 0) :
    eval rho {choice_name}.y = nativeY := by
  have option := {choice_name}.native_choice cardinality rho one four {satisfies(0)}
    nativeOption sqrtSpecification
  have square := {choice_name}.selected_square rho one four {satisfies(0)}
  have parity := actual_parity codec rho one four satisfied
  rw [option] at square parity
  exact ElligatorNative.codec_root_unique codec _ _
    (square.trans nativeSquare.symm) (parity.trans nativeParity.symm)

theorem native_image {{F : Type}} [Field F] [CharP F {choice_name}.modulus]
    [Fintype F] [DecidableEq F]
    (codec : TransferReduction.CanonicalField F) (cardinality : Fintype.card F = {choice_name}.modulus)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) (nativeOption : Bool) (nativeY : F)
    (sqrtSpecification : nativeOption = true ↔ ∃ root : F, root * root = eval rho {choice_name}.gx1)
    (nativeSquare : nativeY * nativeY =
      if nativeOption then eval rho {choice_name}.gx1 else eval rho {choice_name}.gx2)
    (nativeParity : codec.decode nativeY % 2 = if nativeOption then 1 else 0) :
    {image_name}.actualImage rho = Elligator.rationalPoint
      ((RuntimeElligatorAlgebra.k : F) * nativeSelectedX rho nativeOption)
      ((RuntimeElligatorAlgebra.k : F) * nativeY) := by
  have image := {image_name}.rational_image rho one four {satisfies(2)}
  have root := native_root_unique codec cardinality rho one four satisfied
    nativeOption nativeY sqrtSpecification nativeSquare nativeParity
  have option := {choice_name}.native_choice cardinality rho one four {satisfies(0)}
    nativeOption sqrtSpecification
  have selected := {choice_name}.selected_x rho one four {satisfies(0)}
  change eval rho {choice_name}.x =
    (if {choice_name}.choice rho then eval rho {choice_name}.x1 else eval rho {choice_name}.x2) at selected
  rw [option] at selected
  have sValue := Compiler.canonical_equal rho {linear(checked['values']['s'])}
    (scaleLinear RuntimeElligatorAlgebra.k {choice_name}.x) (by decide)
  have tValue := Compiler.canonical_equal rho {linear(checked['values']['t'])}
    (scaleLinear RuntimeElligatorAlgebra.k {choice_name}.y) (by decide)
  rw [eval_scale,selected] at sValue
  rw [eval_scale,root] at tValue
  rw [sValue,tValue] at image
  exact image
'''
    exports += ['actual_parity', 'native_root_unique', 'native_image']
    source += ''.join('#print axioms ' + export + '\n' for export in exports)
    return name, _signature_audits(source + 'end ShielddSecurity.' + name + '\n')
