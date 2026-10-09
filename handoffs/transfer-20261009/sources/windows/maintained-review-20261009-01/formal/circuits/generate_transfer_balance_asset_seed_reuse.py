"""Actual same-map source object/reseed join, without another ordinary scan.

Both already qualified native source views must be independently reaccepted.
The native asset point is the owned value_generator program's result, not an
arbitrary point with a supplied desired coordinate. Global SDK hash/map ABI
interpretations remain named contracts. No candidate is saved by this module.
"""
import re
from . import transfer_relation as relation, transfer_asset_generator_nonidentity as asset
from . import transfer_balance_variable as variable
from .transfer_balance_final_add import DIGEST
from .generate_hash_round import _signature_audits


def generate(variable_parent, variable_pages, signed, asset_base, map_parent, accepted_roles):
    checked = variable.inspect_pages(variable_parent, variable_pages, DIGEST, signed, asset_base)
    mapped = asset.inspect_metadata(map_parent, accepted_roles)
    coordinates = []
    for axis, ref in enumerate(mapped['metadata']['cofactor'][3]):
        if ref != asset_base[axis] or 'source' not in ref:
            raise relation.RelationError('balance same-map exact final cofactor source object required')
        source = tuple(ref['source'])
        lc = checked['chunks'][0]['derived'].get(source)
        if lc != mapped['points'][3][axis] or lc != (((190237, 190241)[axis], 1),):
            raise relation.RelationError('balance same-map exact original singleton LC correspondence')
        coordinates.append(lc[0][0])
    return _source(checked['parent_sha256'], mapped['metadata_sha256'], coordinates)


def _parameter_declaration(body, namespace):
    """Exact complete signed table source, not digest-only correspondence."""
    if (not isinstance(body, str) or
            body.count('namespace ShielddSecurity.'+namespace+'\n') != 1 or
            body.count('def parameters : Poseidon.Parameters Int 3 where\n') != 1 or
            re.search(r'\b(?:sorry|admit|axiom|native_decide)\b', body)):
        raise relation.RelationError('balance owned asset exact qualified parameter source shape')
    start = body.index('def parameters : Poseidon.Parameters Int 3 where\n')
    tail = body[start:]
    end = re.search(r'\n(?:def |end ShielddSecurity\.)', tail)
    if end is None:
        raise relation.RelationError('balance owned asset complete parameter declaration')
    return tail[:end.start()].strip()


def generate_owned(variable_parent, variable_pages, signed, asset_base, map_parent,
                   accepted_roles, actual_hash_data, native_hash_data):
    """Additive owned source join; both Data bodies need qualified root receipts.

    The original source/native metadata acceptance is unchanged. Full table
    declarations are compared here, and the generated proof independently
    checks their equality. No runtime candidate or qualification flag is saved.
    """
    name, legacy = generate(variable_parent, variable_pages, signed, asset_base,
                            map_parent, accepted_roles)
    _check_parameter_correspondence(actual_hash_data, native_hash_data)
    return _owned_source(name, legacy)


def _check_parameter_correspondence(actual_hash_data, native_hash_data):
    actual = _parameter_declaration(actual_hash_data,
        'RuntimeHashBlock_balance0_asset0_permutation0_0')
    native = _parameter_declaration(native_hash_data,
        'RuntimeHashBlock_authorization_rnk_permutation2_0')
    if actual != native:
        raise relation.RelationError('balance owned asset every signed ARK/MDS entry and fallback must match')


def _owned_source(name, legacy):
    """Preserve the default renderer; replace its conditional ABI application."""
    owned = 'RuntimeBalanceOwnedAssetSeedReuse'
    source = legacy.replace('import ShielddSecurity.NativeAssetValueGenerator\n',
        'import ShielddSecurity.NativeAssetGeneratorSource\n', 1)
    source = source.replace('ShielddSecurity.'+name, 'ShielddSecurity.'+owned)
    old_context = 'variable (abi : NativeAssetValueGenerator.HashMapABI upstream hashSpec (mapSpec codec sdkApi))'
    context = '''variable {HexEncoded : Type}
variable (hex : ShielddNativeParameterBytes.HexCodec HexEncoded)
variable (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
variable (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
variable (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
variable (ops : NativeAssetMap.Primitives fq sdkApi)
variable (points : NativeAssetMap.PointPrimitives fq upstream)
'''
    if source.count(old_context) != 1:
        raise relation.RelationError('balance owned asset exact legacy context')
    source = source.replace(old_context, context)
    old_object = 'NativeAssetValueGenerator.valueGenerator abi asset'
    new_object = 'NativeAssetGeneratorSource.valueGenerator hex fq arithmetic initial square sdkApi ops upstream points asset'
    if source.count(old_object) != 6:
        raise relation.RelationError('balance owned asset exact same-object occurrences')
    # The legacy local rho was called initial. Keep the SDK SdkInitial object
    # distinct when the owned source theorem is invoked below.
    proof_start = source.index('theorem constructed_coordinates ')
    proof_end = source.index('theorem reseed_unchanged ', proof_start)
    source = (source[:proof_start] + re.sub(r'\binitial\b', 'sourceRho',
        source[proof_start:proof_end]) + source[proof_end:])
    source = source.replace(old_object, new_object)
    source = source.replace('Global unmodified SDK hash/map ABI, backend and parameter-object laws remain',
        'Owned hash/map bodies are proved; global upstream primitive/codec/curve laws remain')
    facts = '''theorem parameter_table :
    NativeAssetHashParameters.smallParameters =
      (Poseidon.castParameters RuntimeHashBlock_balance0_asset0_permutation0_0.parameters : Poseidon.Parameters F 3) := by
  rfl

theorem coefficient_k : (RuntimeElligatorAlgebra.k : F) = NativeAssetMap.coefficientK := by
  have scale := RuntimeElligatorAlgebra.scale (F := F)
  norm_num only [RuntimeElligatorAlgebra.j,Int.cast_ofNat] at scale
  simpa only [NativeAssetMap.coefficientK] using scale

theorem coefficient_c1 : (RuntimeElligatorAlgebra.c1 : F) = NativeAssetMap.coefficientC1 := by
  apply mul_left_cancel₀ (RuntimeElligatorAlgebra.k_nonzero (F := F))
  rw [RuntimeElligatorAlgebra.first]
  unfold NativeAssetMap.coefficientC1
  rw [← coefficient_k]
  calc
    (RuntimeElligatorAlgebra.j : F) = (40962 : F) := by norm_num [RuntimeElligatorAlgebra.j]
    _ = 40962 * ((RuntimeElligatorAlgebra.k : F) * (RuntimeElligatorAlgebra.k : F)⁻¹) := by
      rw [mul_inv_cancel₀ RuntimeElligatorAlgebra.k_nonzero,mul_one]
    _ = _ := by ring

theorem coefficient_c2 : (RuntimeElligatorAlgebra.c2 : F) = NativeAssetMap.coefficientC2 := by
  apply mul_left_cancel₀ (mul_ne_zero (RuntimeElligatorAlgebra.k_nonzero (F := F))
    (RuntimeElligatorAlgebra.k_nonzero (F := F)))
  rw [RuntimeElligatorAlgebra.second]
  unfold NativeAssetMap.coefficientC2
  rw [← coefficient_k]
  calc
    (1 : F) = ((RuntimeElligatorAlgebra.k : F) * (RuntimeElligatorAlgebra.k : F)⁻¹) *
        ((RuntimeElligatorAlgebra.k : F) * (RuntimeElligatorAlgebra.k : F)⁻¹) := by
      rw [mul_inv_cancel₀ RuntimeElligatorAlgebra.k_nonzero,one_mul]
    _ = _ := by ring

'''
    marker='theorem source_input '
    if source.count(marker) != 1:
        raise relation.RelationError('balance owned asset exact insertion point')
    source = source.replace(marker, facts+marker, 1)
    old_proof = '(NativeAssetValueGenerator.coordinates upstream abi asset).symm'
    proof = '''by
      have denominator : Group.NoUnitSquare (-5 : F) := by
        have residue := Compiler.coefficient_mod (F := F) (p := Scalar.modulus) (-5)
        have checked : (-5 : Int) % (Scalar.modulus : Int) = RuntimeElligatorParameters.negative_z := by decide
        rw [checked] at residue
        have negative := RuntimeElligatorParameters.negative_z_nonsquare (F := F) cardinality
        rw [residue] at negative
        simpa only [Int.cast_neg,Int.cast_ofNat] using negative
      have nonzero : (NativeAssetMap.coefficientK : F) ≠ 0 := by
        rw [← coefficient_k]
        exact RuntimeElligatorAlgebra.k_nonzero
      have edwards : (NativeAssetMap.coefficientK : F) * (RuntimeJubjub.d : F) = 40960 := by
        rw [← coefficient_k]
        have result := RuntimeElligatorAlgebra.edwards (F := F)
        norm_num only [RuntimeElligatorAlgebra.j,Int.cast_ofNat] at result
        exact result
      have native := NativeAssetGeneratorSource.coordinates hex fq arithmetic initial square codec sdkApi ops upstream points
        (RuntimeJubjub.imaginary : F) (RuntimeJubjub.nonsquare cardinality) RuntimeJubjub.imaginary_square
        nonzero denominator edwards RuntimeTransferAssetMapNativeSeeds.field_odd
        RuntimeTransferAssetMapNativeSeeds.five_nonzero (RuntimeTransferAssetMapNativeSeeds.five_euler cardinality) asset
      simpa only [hashSpec,RuntimeTransferAssetMapHashJoin.nativeAssetGenerator,
        RuntimeTransferAssetMapLegalCompletion.nativeGenerator,← parameter_table,
        ← coefficient_k,← coefficient_c1,← coefficient_c2] using native.symm'''
    if source.count(old_proof) != 1:
        raise relation.RelationError('balance owned asset exact final source proof')
    source = source.replace(old_proof, proof)
    source = source.replace('constructed_coordinates fq fr model upstream codec circuitApi sdkApi abi cardinality',
        'constructed_coordinates fq fr model upstream codec circuitApi sdkApi hex arithmetic initial square ops points cardinality')
    ending='end ShielddSecurity.'+owned+'\n'
    if not source.endswith(ending) or 'HashMapABI' in source or 'NativeAssetValueGenerator.' in source:
        raise relation.RelationError('balance owned asset complete source body required')
    extra=''.join('#print axioms '+export+'\n' for export in
                  ('parameter_table','coefficient_k','coefficient_c1','coefficient_c2'))
    return owned, _signature_audits(source[:-len(ending)]+extra+ending)


def _source(variable_sha, map_sha, columns):
    if columns != [190237, 190241]:
        raise relation.RelationError('balance same-map production cofactor columns required')
    name = 'RuntimeBalanceAssetSeedReuse'
    source = f'''import ShielddSecurity.NativeAssetValueGenerator
import ShielddSecurity.ShielddPointCoordinateSeed
import ShielddSecurity.RuntimeTransferCompleteAssetConeInterop
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Independently accepted variable5 parent {variable_sha}, map parent {map_sha}.
-- Exact source LC association190237/190241; hash/map semantics are proved below.
-- Global unmodified SDK hash/map ABI, backend and parameter-object laws remain
-- explicit. Identity outputs are permitted here; legal asset proof-data and
-- native balance success separately justify the inverse/full-row domain.
variable {{F E S R K Q Signing J Encoded Native : Type}}
variable [Field F] [CharP F Scalar.modulus] [DecidableEq F] [Fintype F] [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (model : Group.StandardCurveModel J (RuntimeJubjub.d : F))
variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr (RuntimeJubjub.d : F) model)
variable (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
variable (codec : TransferReduction.CanonicalField F) (circuitApi sdkApi : ElligatorNativeRoots.SqrtAPI F)
def hashSpec (value : F) : F :=
  Poseidon.hash3 (Poseidon.castParameters RuntimeHashBlock_balance0_asset0_permutation0_0.parameters) 26 [value]
def mapSpec (value : F) : Group.Point F := RuntimeTransferAssetMapLegalCompletion.nativeGenerator codec sdkApi value
variable (abi : NativeAssetValueGenerator.HashMapABI upstream hashSpec (mapSpec codec sdkApi))
def sourceAssignment (base : Nat → F) (asset : Q) : Nat → F := Function.update base 6 (fq.integer asset : F)
def assetAssignment (base : Nat → F) (asset : Q) : Nat → F :=
  RuntimeTransferCompleteAssetCone.completeAssignment codec circuitApi (sourceAssignment fq base asset)
def point (rho : Nat → F) : Group.Point F := ⟨rho 190237,rho 190241⟩
theorem source_input (base : Nat → F) (asset : Q) : sourceAssignment fq base asset 6 = (fq.integer asset : F) := by
  simp [sourceAssignment,Function.update]
theorem source_one (base : Nat → F) (asset : Q) (one : base 0 = 1) : sourceAssignment fq base asset 0 = 1 := by
  simp [sourceAssignment,one]
theorem constructed_coordinates (cardinality : Fintype.card F = Scalar.modulus)
    (base : Nat → F) (asset : Q) (one : base 0 = 1) (four : (4 : F) ≠ 0) :
    point (assetAssignment fq codec circuitApi base asset) =
      model.coordinates (upstream.embed (upstream.promote (NativeAssetValueGenerator.valueGenerator abi asset))) := by
  let initial := RuntimeTransferAssetNonzero.completeAssignment (sourceAssignment fq base asset)
  let hashed := RuntimeTransferAssetMapHashJoin.hashAssignment initial
  let mapped := RuntimeTransferAssetMapNativeCompletion.completeAssignment codec circuitApi hashed
  have initialOne : initial 0 = 1 :=
    (RuntimeTransferAssetNonzero.complete_preserves_roles (sourceAssignment fq base asset)).1.trans (source_one fq base asset one)
  have initialCopy : initial 200692 = 1 := by
    simp [initial,RuntimeTransferAssetNonzero.completeAssignment]
  have initialLinked : initial 200692 = initial 0 := initialCopy.trans initialOne.symm
  have initialAsset : initial 6 = (fq.integer asset : F) :=
    (RuntimeTransferAssetNonzero.complete_preserves_roles (sourceAssignment fq base asset)).2.2.2.trans (source_input fq base asset)
  have hashedOne := RuntimeTransferAssetMapHashJoin.hash_one initial initialOne
  have hashedLinked := RuntimeTransferAssetMapHashJoin.hash_linked initial initialLinked
  have built := RuntimeTransferAssetMapNativeCompletion.native_cofactor cardinality codec circuitApi hashed hashedOne four hashedLinked
  have mapPoint : point mapped = RuntimeTransferAssetMapNativeSeeds.nativePoint3 codec circuitApi hashed := by
    simpa only [point,RuntimeTransferAssetMapNativeDouble2.output,eval,Int.cast_one,one_mul,add_zero] using built
  have preserved : point (assetAssignment fq codec circuitApi base asset) = point mapped := by
    change point (RuntimeTransferAssetGeneratorInverseCompletion.completeAssignment mapped) = point mapped
    exact congrArg₂ Group.Point.mk
      (RuntimeTransferAssetGeneratorInverseCompletion.preserves mapped 190237 (by decide))
      (RuntimeTransferAssetGeneratorInverseCompletion.preserves mapped 190241 (by decide))
  have native := RuntimeTransferAssetMapLegalCompletion.native_generator_value cardinality codec circuitApi hashed
  have input := RuntimeTransferAssetMapHashJoin.map_input_value initial initialOne initialLinked
  have inputAsset : eval initial RuntimeTransferAssetMapHashJoin.asset = (fq.integer asset : F) := by
    simpa only [RuntimeTransferAssetMapHashJoin.asset,eval,Int.cast_one,one_mul,add_zero] using initialAsset
  have agreement := RuntimeTransferCompleteAssetConeInterop.hashed_generators_agree cardinality codec circuitApi sdkApi initial initialOne initialLinked
  rw [inputAsset] at input agreement
  calc
    _ = RuntimeTransferAssetMapNativeSeeds.nativePoint3 codec circuitApi hashed := preserved.trans mapPoint
    _ = RuntimeTransferAssetMapLegalCompletion.nativeGenerator codec circuitApi
        (RuntimeTransferAssetMapFirstCubicConstruction.nativeInput hashed) := native.symm
    _ = RuntimeTransferAssetMapHashJoin.nativeAssetGenerator codec circuitApi (fq.integer asset : F) := by
      rw [input]; rfl
    _ = RuntimeTransferAssetMapHashJoin.nativeAssetGenerator codec sdkApi (fq.integer asset : F) := agreement
    _ = model.coordinates (upstream.embed (upstream.promote (NativeAssetValueGenerator.valueGenerator abi asset))) :=
      (NativeAssetValueGenerator.coordinates upstream abi asset).symm
theorem reseed_unchanged (cardinality : Fintype.card F = Scalar.modulus)
    (base : Nat → F) (asset : Q) (one : base 0 = 1) (four : (4 : F) ≠ 0) :
    ShielddPointCoordinateSeed.seed fq fr (RuntimeJubjub.d : F) model upstream backend
      (NativeAssetValueGenerator.valueGenerator abi asset) 190237 190241
      (assetAssignment fq codec circuitApi base asset) = assetAssignment fq codec circuitApi base asset := by
  let rho := assetAssignment fq codec circuitApi base asset
  let seeded := ShielddPointCoordinateSeed.seed fq fr (RuntimeJubjub.d : F) model upstream backend
    (NativeAssetValueGenerator.valueGenerator abi asset) 190237 190241 rho
  have derived := constructed_coordinates fq fr model upstream codec circuitApi sdkApi abi cardinality base asset one four
  have read := ShielddPointCoordinateSeed.coordinates fq fr (RuntimeJubjub.d : F) model upstream backend
    (NativeAssetValueGenerator.valueGenerator abi asset) 190237 190241 (by decide) rho
  have agreement : (⟨seeded 190237,seeded 190241⟩ : Group.Point F) = point rho := read.trans derived.symm
  funext column
  by_cases x : column = 190237
  · subst column
    exact congrArg Group.Point.x agreement
  · by_cases y : column = 190241
    · subst column
      exact congrArg Group.Point.y agreement
    · exact ShielddPointCoordinateSeed.seed_preserves fq fr (RuntimeJubjub.d : F) model upstream backend
        (NativeAssetValueGenerator.valueGenerator abi asset) 190237 190241 rho column
        (by simp only [ShielddPointCoordinateSeed.columns,List.mem_cons,List.not_mem_nil,or_false]; exact not_or.mpr ⟨x,y⟩)
'''
    for export in ('source_input', 'source_one', 'constructed_coordinates', 'reseed_unchanged'):
        source += '#print axioms ' + export + '\n'
    return name, _signature_audits(source + f'end ShielddSecurity.{name}\n')
