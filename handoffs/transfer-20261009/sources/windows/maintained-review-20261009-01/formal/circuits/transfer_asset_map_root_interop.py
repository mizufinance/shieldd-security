"""Actual owned map point agrees across independently sound/complete sqrt APIs."""
from . import transfer_asset_map_native_completion as completion


def generate(data, extracted, accepted_roles):
    return _from_checked(completion.plan(data, extracted, accepted_roles)['recipe'])


def _from_checked(recipe):
    """Compose imported actual theorems from their retained checked source receipt."""
    from .generate_hash_round import _signature_audits
    name = 'RuntimeTransferAssetMapRootInterop'
    core = 'RuntimeTransferAssetMapFirstCubicConstruction'
    native = 'RuntimeTransferAssetMapNativeSeeds'
    source = f'''import ShielddSecurity.RuntimeTransferAssetMapNativeSource
import ShielddSecurity.ElligatorNativeRootInterop
set_option maxHeartbeats 250000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact accepted source metadata SHA256 {recipe['checked']['metadata_sha256']}.
-- Both global native ABI contracts are independent; no raw-root equality.
abbrev modulus := {native}.modulus
variable {{F : Type}} [Field F] [CharP F modulus] [DecidableEq F]

theorem source_first_nonzero [Fintype F] (cardinality : Fintype.card F = modulus)
    (rho : Nat → F) : ElligatorNativeProgram.firstCubic (RuntimeElligatorAlgebra.c1 : F)
      (RuntimeElligatorAlgebra.c2 : F) ({core}.nativeInput rho) ≠ 0 := by
  change {core}.nativeFirst rho ≠ 0
  exact {core}.native_first_nonzero cardinality rho

theorem native_source_apis_agree [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F)
    (left right : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) :
    ElligatorNativeProgram.sourceProgram codec left (RuntimeElligatorAlgebra.c1 : F)
      (RuntimeElligatorAlgebra.c2 : F) (RuntimeElligatorAlgebra.k : F) (RuntimeJubjub.d : F)
      ({core}.nativeInput rho) =
    ElligatorNativeProgram.sourceProgram codec right (RuntimeElligatorAlgebra.c1 : F)
      (RuntimeElligatorAlgebra.c2 : F) (RuntimeElligatorAlgebra.k : F) (RuntimeJubjub.d : F)
      ({core}.nativeInput rho) :=
  ElligatorNativeRootInterop.source_program_agreement codec left right
    ({native}.field_odd (F := F)) ({native}.five_nonzero (F := F)) ({native}.five_euler cardinality)
    (RuntimeElligatorAlgebra.c1 : F) (RuntimeElligatorAlgebra.c2 : F)
    (RuntimeElligatorAlgebra.k : F) (RuntimeJubjub.d : F) ({core}.nativeInput rho)
    (source_first_nonzero cardinality rho)

theorem actual_other_api [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F)
    (circuitApi sdkApi : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {recipe['checked']['metadata']['constant_copy']} = rho 0) :
    ElligatorNativeProgram.sourceProgram codec sdkApi (RuntimeElligatorAlgebra.c1 : F)
      (RuntimeElligatorAlgebra.c2 : F) (RuntimeElligatorAlgebra.k : F) (RuntimeJubjub.d : F)
      ({core}.nativeInput rho) = some (RuntimeTransferAssetMapNativeDouble2.output
        (RuntimeTransferAssetMapNativeCompletion.completeAssignment codec circuitApi rho)) := by
  rw [native_source_apis_agree cardinality codec sdkApi circuitApi rho]
  exact RuntimeTransferAssetMapNativeSource.actual_native_program cardinality codec circuitApi rho one four linked
'''
    exports = ['source_first_nonzero', 'native_source_apis_agree', 'actual_other_api']
    source += ''.join('#print axioms ' + export + '\n' for export in exports)
    return name, _signature_audits(source + 'end ShielddSecurity.' + name + '\n')
