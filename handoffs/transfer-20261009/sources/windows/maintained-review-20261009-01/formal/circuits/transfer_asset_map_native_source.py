"""Actual constructed map output follows the pinned partial native program."""
from . import transfer_asset_map_native_completion as completion


def generate(data,extracted,accepted_roles):
    from .generate_hash_round import _signature_audits
    recipe=completion.plan(data,extracted,accepted_roles)['recipe']
    name='RuntimeTransferAssetMapNativeSource';native='RuntimeTransferAssetMapNativeSeeds'
    core='RuntimeTransferAssetMapFirstCubicConstruction';full='RuntimeTransferAssetMapNativeCompletion'
    copy=recipe['checked']['metadata']['constant_copy']
    source=f'''import ShielddSecurity.{full}
import ShielddSecurity.ElligatorNativeProgram
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact actual metadata SHA256 {recipe['checked']['metadata_sha256']}.
-- Native sqrt and BE codec are global function interfaces. Actual domain26
-- hash/asset input correspondence and their FFI instantiation remain separate.
abbrev modulus := {native}.modulus
variable {{F : Type}} [Field F] [CharP F modulus] [DecidableEq F]

theorem native_eight (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) :
    {native}.nativePoint3 codec api rho = GroupNativeCofactor.nativeEight (RuntimeJubjub.d : F)
      ({native}.nativeImage codec api rho) := rfl

theorem native_program [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) :
    ElligatorNativeProgram.sourceProgram codec api (RuntimeElligatorAlgebra.c1 : F)
      (RuntimeElligatorAlgebra.c2 : F) (RuntimeElligatorAlgebra.k : F) (RuntimeJubjub.d : F)
      ({core}.nativeInput rho) = some ({native}.nativePoint3 codec api rho) := by
  have defined := ElligatorNativeProgram.source_defined codec api
    ({native}.field_odd (F := F)) ({native}.five_nonzero (F := F)) ({native}.five_euler cardinality)
    (RuntimeElligatorAlgebra.c1 : F) (RuntimeElligatorAlgebra.c2 : F)
    (RuntimeElligatorAlgebra.k : F) (RuntimeJubjub.d : F) ({core}.nativeInput rho)
  simpa only [ElligatorNativeProgram.generatorValue,ElligatorNativeProgram.firstX,
    ElligatorNativeProgram.firstCubic,{native}.nativePoint3,{native}.nativePoint2,{native}.nativePoint1,
    {native}.nativeImage,{native}.nativeY,{native}.rawNativeY,{native}.nativeSelectedX,
    {native}.nativeChoice,{core}.nativeFirst,{core}.nativeX,{core}.nativeInverse,{core}.nativeTv,
    GroupNativeCofactor.nativeEight] using defined

theorem actual_native_program [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    ElligatorNativeProgram.sourceProgram codec api (RuntimeElligatorAlgebra.c1 : F)
      (RuntimeElligatorAlgebra.c2 : F) (RuntimeElligatorAlgebra.k : F) (RuntimeJubjub.d : F)
      ({core}.nativeInput rho) = some (RuntimeTransferAssetMapNativeDouble2.output
        ({full}.completeAssignment codec api rho)) := by
  rw [{full}.native_cofactor cardinality codec api rho one four linked]
  exact native_program cardinality codec api rho

theorem encoded_native_root (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) :
    ElligatorNativeProgram.encodedNormalize codec writer ({native}.nativeChoice api rho)
      ({native}.rawNativeY api rho) = {native}.nativeY codec api rho :=
  ElligatorNativeProgram.encoded_normalize codec writer _ _
'''
    exports=['native_eight','native_program','actual_native_program','encoded_native_root']
    source+=''.join('#print axioms '+export+'\n' for export in exports)
    return name,_signature_audits(source+'end ShielddSecurity.'+name+'\n')
