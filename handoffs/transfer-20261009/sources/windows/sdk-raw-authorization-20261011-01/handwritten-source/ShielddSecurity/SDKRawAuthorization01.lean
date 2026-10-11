import ShielddSecurity.SDKNativeSpendAuth01
import ShielddSecurity.ShielddNativeAuthorizationRaw
import Mathlib.Data.List.OfFn

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true

namespace ShielddSecurity.SDKRawAuthorization01
open ConcreteJubjubField01 ConcretePointTorsion01 ConcreteCofactorModel01

variable {Raw Encoded E S R K Q Signing : Type}
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}

variable (operations : ShielddNativeScalar.Operations (F := F) Raw)
  (read : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
  (write : ShielddNativeEncode.Primitives (Encoded := Encoded) operations)
  (upstream : ShielddNativeSdk.Upstream E S R K Q Signing curve.Point fq fr coefficient model)
  (standard : SDKNativeSpendAuth01.StandardCoordinates upstream)

attribute [local irreducible] GroupNativeAuthorization.nativeAuthorization
  GroupNativeMultiply.nativeMultiply SDKJubjubMultiply01.multiply SDKJubjubMultiply01.encodedBits

def bytesList (bytes : GroupByteCodec.Bytes) : List Nat :=
  List.ofFn (fun index : Fin 32 => (bytes index).val)

theorem bytes_list_injective (left right : GroupByteCodec.Bytes)
    (same : bytesList left = bytesList right) : left = right := by
  have equalValues : (fun index : Fin 32 => (left index).val) =
      (fun index : Fin 32 => (right index).val) := List.ofFn_injective same
  funext index
  exact Fin.ext (congrFun equalValues index)

/-- Encoding injectivity is derived from a global byte/coordinate primitive
refinement, rather than supplied as an abstract SDK group axiom. This global
Rust representation correspondence is explicitly still a boundary contract. -/
theorem encoding_injective (embed : K → curve.Point) (encode : K → GroupByteCodec.Bytes)
    (meaning : ∀ key, bytesList (encode key) = SDKEncodingInjective01.encode (model.coordinates (embed key)))
    (left right : K) (same : encode left = encode right) : embed left = embed right := by
  apply model.injective
  apply SDKEncodingInjective01.encoding_injective _ _ (model.onCurve _) (model.onCurve _)
  rw [← meaning left, ← meaning right, same]

theorem encoding_coherent (embed : K → curve.Point) (encode : K → GroupByteCodec.Bytes)
    (meaning : ∀ key, bytesList (encode key) = SDKEncodingInjective01.encode (model.coordinates (embed key)))
    (left right : K) (same : embed left = embed right) : encode left = encode right := by
  apply bytes_list_injective
  rw [meaning left, meaning right, same]

/-- Mathematical compressed admission recovers subgroup/nonidentity for the
actual decoded key under the global byte refinement. No abstract SDK subgroup
decoder law or per-key desired group equation is a premise. -/
theorem key_admission (embed : K → curve.Point) (encode : K → GroupByteCodec.Bytes)
    (meaning : ∀ key, bytesList (encode key) = SDKEncodingInjective01.encode (model.coordinates (embed key)))
    (key : K) (input : Group.Point F)
    (accepted : SDKCompressedAdmission01.Accepted (bytesList (encode key)) input) :
    Scalar.order • embed key = 0 ∧ embed key ≠ 0 := by
  have inputCoordinates := SDKCompressedAdmission01.admitted_point_unique
    (bytesList (encode key)) input accepted (embed key) (meaning key).symm
  obtain ⟨point, coordinates, subgroup, nonidentity⟩ := SDKCompressedAdmission01.admission_sound
    (bytesList (encode key)) input accepted
  have same : point = embed key := model.injective (coordinates.trans inputCoordinates)
  exact same ▸ ⟨subgroup, nonidentity⟩

include standard in
theorem raw_generator_read :
    (ShielddNativeSdkRaw.generator operations read upstream).map
      (ShielddNativePoint.pointValue operations) = some SDKSpendAuthCertificates01.sdkBase := by
  rw [ShielddNativeSdkRaw.generator_value]
  exact SDKNativeSpendAuth01.generator_read upstream standard
    (ShielddNativeScalar.readerBackend operations read)

theorem raw_scalar_read (randomizer : R) :
    (ShielddNativeSdkRaw.scalar (fq := fq) (fr := fr) operations read randomizer).map
      (ShielddNativeScalar.value operations) = some (fr.integer randomizer : F) := by
  rw [ShielddNativeSdkRaw.scalar_value]
  exact ShielddNativeSdk.scalar_read (fq := fq) (fr := fr)
    (ShielddNativeScalar.readerBackend operations read) randomizer

/-- Owned raw authorization maps to the proved production SDK output. Its
raw reader/scalar/write/arithmetic bodies execute before this conclusion.
This theorem deliberately does not infer output nonidentity from the input. -/
theorem raw_authorization_coordinates (verification : K) (randomizer : R) (point : S)
    (accepted : ShielddNativeSdk.nonidentity upstream (upstream.keyBytes verification) = some point) :
    (ShielddNativeAuthorizationRaw.authorization operations read write upstream verification randomizer).map
      (ShielddNativePoint.pointValue operations) =
    some (model.coordinates (upstream.embed (upstream.keyPoint
      (ShielddNativeSdk.planRk upstream verification randomizer)))) := by
  rw [ShielddNativeAuthorizationRaw.authorization_value operations read write canonical upstream
    SDKNativeSpendAuth01.native_coefficient]
  have coordinates := ShielddNativeAuthorization.owned_authorization_coordinates canonical
    (GroupByteCodec.canonicalWrite canonical) (ShielddNativeScalar.readerBackend operations read)
    upstream imaginary coefficient_no_unit_square imaginary_square two_ne_zero
    verification randomizer point accepted
  rw [← ShielddNativeSdk.plan_randomization upstream verification randomizer] at coordinates
  exact coordinates

theorem raw_authorization_exists (verification : K) (randomizer : R) (point : S)
    (accepted : ShielddNativeSdk.nonidentity upstream (upstream.keyBytes verification) = some point) :
    ∃ output, ShielddNativeAuthorizationRaw.authorization operations read write upstream
      verification randomizer = some output ∧
      ShielddNativePoint.pointValue operations output =
        model.coordinates (upstream.embed (upstream.keyPoint
          (ShielddNativeSdk.planRk upstream verification randomizer))) := by
  have meaning := raw_authorization_coordinates operations read write upstream verification randomizer point accepted
  cases result : ShielddNativeAuthorizationRaw.authorization operations read write upstream verification randomizer with
  | none => simp only [result, Option.map_none] at meaning; cases meaning
  | some output =>
      refine ⟨output, rfl, ?_⟩
      exact Option.some.inj (by simpa only [result, Option.map_some] using meaning)

theorem raw_authorization_agrees (verification : K) (randomizer : R) (input output : S)
    (inputGate : ShielddNativeSdk.nonidentity upstream (upstream.keyBytes verification) = some input)
    (outputGate : ShielddNativeSdk.nonidentity upstream
      (upstream.keyBytes (ShielddNativeSdk.planRk upstream verification randomizer)) = some output) :
    (ShielddNativeAuthorizationRaw.authorization operations read write upstream verification randomizer).map
      (ShielddNativePoint.pointValue operations) =
    ShielddNativeSdk.key (ShielddNativeScalar.readerBackend operations read) upstream
      (ShielddNativeSdk.planRk upstream verification randomizer) := by
  rw [raw_authorization_coordinates operations read write upstream verification randomizer input inputGate,
    ShielddNativeSdk.key_read canonical _ upstream _ output outputGate]

theorem raw_native_constraints (verification : K) (randomizer : R) (input output : S)
    (inputGate : ShielddNativeSdk.nonidentity upstream (upstream.keyBytes verification) = some input)
    (outputGate : ShielddNativeSdk.nonidentity upstream
      (upstream.keyBytes (ShielddNativeSdk.planRk upstream verification randomizer)) = some output) :
    ∃ computed, ShielddNativeAuthorizationRaw.authorization operations read write upstream verification randomizer =
      some computed ∧ SDKCompressedAdmission01.WitnessConstraints (GroupByteCodec.canonicalWrite canonical)
        (ShielddNativePoint.pointValue operations computed) := by
  obtain ⟨computed, result, coordinates⟩ := raw_authorization_exists operations read write upstream
    verification randomizer input inputGate
  refine ⟨computed, result, ?_⟩
  rw [coordinates]
  exact SDKNativeSpendAuth01.production_native_constraints upstream
    (GroupByteCodec.canonicalWrite canonical) verification randomizer output outputGate

/-- A concrete mathematical cancellation witness. This is a proof of the
necessary output gate, not runtime testing or a successful negative control. -/
theorem canceling_input_admitted :
    SDKCompressedAdmission01.Accepted
      (SDKEncodingInjective01.encode (model.coordinates (-SDKSpendAuthSubgroup01.base)))
      (model.coordinates (-SDKSpendAuthSubgroup01.base)) := by
  apply SDKCompressedAdmission01.admission_complete
  · rw [neg_nsmul, SDKSpendAuthSubgroup01.base_subgroup, neg_zero]
  · exact neg_ne_zero.mpr SDKSpendAuthOrder01.base_nonzero

theorem canceling_output_identity :
    SDKJubjubExtended01.isIdentity (SDKJubjubExtended01.affine
      (SDKJubjubExtended01.normalize (SDKSubgroupAdmission01.randomize
        (model.coordinates (-SDKSpendAuthSubgroup01.base)) SDKSpendAuthSubgroup01.base 1))) := by
  rw [SDKSubgroupAdmission01.randomize_coordinates _ _ 1 (by decide), one_nsmul, neg_add_cancel]
  exact (SDKCompressedAdmission01.affine_identity_iff 0).mpr rfl

end ShielddSecurity.SDKRawAuthorization01

set_option pp.all true in
#check @ShielddSecurity.SDKRawAuthorization01.bytesList
#print axioms ShielddSecurity.SDKRawAuthorization01.bytesList
set_option pp.all true in
#check @ShielddSecurity.SDKRawAuthorization01.bytes_list_injective
#print axioms ShielddSecurity.SDKRawAuthorization01.bytes_list_injective
set_option pp.all true in
#check @ShielddSecurity.SDKRawAuthorization01.encoding_injective
#print axioms ShielddSecurity.SDKRawAuthorization01.encoding_injective
set_option pp.all true in
#check @ShielddSecurity.SDKRawAuthorization01.encoding_coherent
#print axioms ShielddSecurity.SDKRawAuthorization01.encoding_coherent
set_option pp.all true in
#check @ShielddSecurity.SDKRawAuthorization01.key_admission
#print axioms ShielddSecurity.SDKRawAuthorization01.key_admission
set_option pp.all true in
#check @ShielddSecurity.SDKRawAuthorization01.raw_generator_read
#print axioms ShielddSecurity.SDKRawAuthorization01.raw_generator_read
set_option pp.all true in
#check @ShielddSecurity.SDKRawAuthorization01.raw_scalar_read
#print axioms ShielddSecurity.SDKRawAuthorization01.raw_scalar_read
set_option pp.all true in
#check @ShielddSecurity.SDKRawAuthorization01.raw_authorization_coordinates
#print axioms ShielddSecurity.SDKRawAuthorization01.raw_authorization_coordinates
set_option pp.all true in
#check @ShielddSecurity.SDKRawAuthorization01.raw_authorization_exists
#print axioms ShielddSecurity.SDKRawAuthorization01.raw_authorization_exists
set_option pp.all true in
#check @ShielddSecurity.SDKRawAuthorization01.raw_authorization_agrees
#print axioms ShielddSecurity.SDKRawAuthorization01.raw_authorization_agrees
set_option pp.all true in
#check @ShielddSecurity.SDKRawAuthorization01.raw_native_constraints
#print axioms ShielddSecurity.SDKRawAuthorization01.raw_native_constraints
set_option pp.all true in
#check @ShielddSecurity.SDKRawAuthorization01.canceling_input_admitted
#print axioms ShielddSecurity.SDKRawAuthorization01.canceling_input_admitted
set_option pp.all true in
#check @ShielddSecurity.SDKRawAuthorization01.canceling_output_identity
#print axioms ShielddSecurity.SDKRawAuthorization01.canceling_output_identity
