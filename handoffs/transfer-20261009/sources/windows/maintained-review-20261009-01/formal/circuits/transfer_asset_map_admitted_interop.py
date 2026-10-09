"""Same original asset cone from separately admitted SDK and circuit sqrt APIs.

Only the existing selected source theorems are composed. No new row extraction,
input role, raw square-root equality or qualification flag is introduced.
"""


def generate():
    from .generate_hash_round import _signature_audits
    name = 'RuntimeTransferCompleteAssetConeInterop'
    whole = 'RuntimeTransferCompleteAssetCone'
    joined = 'RuntimeTransferAssetMapHashJoin'
    legal = 'RuntimeTransferAssetMapLegalCompletion'
    core = 'RuntimeTransferAssetMapFirstCubicConstruction'
    seeds = 'RuntimeTransferAssetMapNativeSeeds'
    early = 'RuntimeTransferAssetNonzero'
    source = f'''import ShielddSecurity.{whole}
import ShielddSecurity.RuntimeTransferAssetMapRootInterop
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Composes exact prior actual hash/map/inverse/earlier rows. The SDK and
-- circuit square-root functions need separate sound/complete contracts only.
abbrev modulus := {whole}.modulus
variable {{F : Type}} [Field F] [CharP F modulus] [DecidableEq F]

theorem hashed_generators_agree [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F) (circuitApi sdkApi : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (one : rho 0 = 1) (linked : rho 200692 = rho 0) :
    {joined}.nativeAssetGenerator codec circuitApi (eval rho {joined}.asset) =
      {joined}.nativeAssetGenerator codec sdkApi (eval rho {joined}.asset) := by
  unfold {joined}.nativeAssetGenerator {legal}.nativeGenerator
  rw [← {joined}.map_input_value rho one linked]
  exact ElligatorNativeRootInterop.generator_agreement codec circuitApi sdkApi
    ({seeds}.field_odd (F := F)) ({seeds}.five_nonzero (F := F)) ({seeds}.five_euler cardinality)
    (RuntimeElligatorAlgebra.c1 : F) (RuntimeElligatorAlgebra.c2 : F)
    (RuntimeElligatorAlgebra.k : F) (RuntimeJubjub.d : F)
    ({core}.nativeInput ({joined}.hashAssignment rho))
    (RuntimeTransferAssetMapRootInterop.source_first_nonzero cardinality ({joined}.hashAssignment rho))

theorem balance_apis_agree [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (circuitApi sdkApi : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (linked : rho 200692 = rho 0)
    (blindingGenerator : Group.Point F) (inputs outputs : NativeTransferAdmission.Amounts) (blinding : F) :
    NativeTransferAdmission.balanceNative codec writer (RuntimeJubjub.d : F)
      ({joined}.nativeAssetGenerator codec circuitApi) blindingGenerator (eval rho {joined}.asset)
      inputs outputs blinding =
    NativeTransferAdmission.balanceNative codec writer (RuntimeJubjub.d : F)
      ({joined}.nativeAssetGenerator codec sdkApi) blindingGenerator (eval rho {joined}.asset)
      inputs outputs blinding := by
  unfold NativeTransferAdmission.balanceNative
  rw [hashed_generators_agree cardinality codec circuitApi sdkApi rho one linked]

theorem complete_rows [Fintype F] (cardinality : Fintype.card F = modulus)
    {{J : Type}} [AddCommGroup J] (model : Group.StandardCurveModel J (RuntimeJubjub.d : F))
    (fullOrder : ∀ point : J, (8 * Scalar.order) • point = 0)
    {{Proof : Type}} (fetch : F → Except NativeAssetAdmission.Error Proof) (proof : Proof)
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (circuitApi sdkApi : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (admitted : NativeAssetAdmission.proofDataNative fetch (rho 6) = .ok proof)
    (blindingGenerator : Group.Point F) (inputs outputs : NativeTransferAdmission.Amounts)
    (blinding : F) (balance : Group.Point F)
    (accepted : NativeTransferAdmission.balanceNative codec writer (RuntimeJubjub.d : F)
      ({joined}.nativeAssetGenerator codec sdkApi) blindingGenerator (eval rho {joined}.asset)
      inputs outputs blinding = .ok balance) :
    Satisfies ({whole}.completeAssignment codec circuitApi rho) {whole}.rawRows := by
  have initialOne : {whole}.initialAssignment rho 0 = 1 :=
    ({early}.complete_preserves_roles rho).1.trans one
  have initialCopy : {whole}.initialAssignment rho 200692 = 1 := by
    simp [{whole}.initialAssignment,{early}.completeAssignment]
  have initialAsset : eval ({whole}.initialAssignment rho) {joined}.asset = eval rho {joined}.asset := by
    rw [{whole}.asset_exact]
    simp only [eval,Int.cast_one,one_mul,add_zero]
    exact ({early}.complete_preserves_roles rho).2.2.2
  have agreeing := balance_apis_agree cardinality codec writer circuitApi sdkApi
    ({whole}.initialAssignment rho) initialOne (initialCopy.trans initialOne.symm)
    blindingGenerator inputs outputs blinding
  rw [initialAsset] at agreeing
  exact {whole}.complete_rows cardinality model fullOrder fetch proof codec writer circuitApi rho one four
    admitted blindingGenerator inputs outputs blinding balance (agreeing.trans accepted)
'''
    exports = ['hashed_generators_agree', 'balance_apis_agree', 'complete_rows']
    source += ''.join('#print axioms ' + export + '\n' for export in exports)
    return name, _signature_audits(source + 'end ShielddSecurity.' + name + '\n')
