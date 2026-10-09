"""Actual native cofactor constructor with derived canonical sign/parity.

Native sqrt-option/selected-square source contracts remain explicit, while the
sign flip and final generator are computed by the constructor. Neither parity,
the circuit selected root nor the desired map/subgroup result is a premise.
"""
from . import transfer_asset_map_cofactor as cofactor


def generate(data, extracted, accepted_roles):
    from .generate_hash_round import _signature_audits
    dependency, _ = cofactor.generate_native(data, extracted, accepted_roles)
    name = 'RuntimeTransferAssetMapNativeConstruction'
    source = f'''import ShielddSecurity.{dependency}
import ShielddSecurity.ElligatorNativeParity
set_option maxHeartbeats 300000
namespace ShielddSecurity.{name}
def rawRows : List Row := {dependency}.rawRows

noncomputable def nativeGenerator {{F : Type}} [Field F] [CharP F Scalar.modulus]
    [DecidableEq F] (codec : TransferReduction.CanonicalField F)
    (rho : Nat → F) (nativeOption : Bool) (nativeRoot : F) : Group.Point F :=
  GroupNativeCofactor.nativeEight (RuntimeJubjub.d : F) (Elligator.rationalPoint
    ((RuntimeElligatorAlgebra.k : F) * RuntimeTransferAssetMapNativeRoot.nativeSelectedX rho nativeOption)
    ((RuntimeElligatorAlgebra.k : F) * ElligatorNativeParity.normalizeRoot codec nativeOption nativeRoot))

theorem native_constructor {{F : Type}} [Field F] [CharP F Scalar.modulus]
    [Fintype F] [DecidableEq F] (codec : TransferReduction.CanonicalField F)
    (cardinality : Fintype.card F = Scalar.modulus) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows)
    (nativeOption : Bool) (nativeRoot : F)
    (sqrtSpecification : nativeOption = true ↔ ∃ root : F, root * root = eval rho RuntimeTransferAssetMapChoice.gx1)
    (nativeSquare : nativeRoot * nativeRoot = if nativeOption then eval rho RuntimeTransferAssetMapChoice.gx1
      else eval rho RuntimeTransferAssetMapChoice.gx2) :
    RuntimeTransferAssetMapDouble2.output rho = nativeGenerator codec rho nativeOption nativeRoot := by
  have coreRows : Satisfies rho RuntimeTransferAssetMapNativeRoot.rawRows :=
    fun row member => satisfied row (List.mem_append.mpr (Or.inr member))
  have firstNonzero := RuntimeTransferAssetMapChoice.cubic_nonzero cardinality rho one four
    (fun row member => coreRows row (RuntimeTransferAssetMapNativeRoot.included0 row member))
  have normalization := ElligatorNativeParity.selected_normalization codec nativeOption
    (eval rho RuntimeTransferAssetMapChoice.gx1) (eval rho RuntimeTransferAssetMapChoice.gx2)
    nativeRoot firstNonzero nativeSquare
  exact {dependency}.native_cofactor codec cardinality rho one four satisfied nativeOption
    (ElligatorNativeParity.normalizeRoot codec nativeOption nativeRoot) sqrtSpecification
    normalization.1 normalization.2
#print axioms native_constructor
end ShielddSecurity.{name}
'''
    return name, _signature_audits(source)
