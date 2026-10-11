import ShielddSecurity.GroupNativeAuthorization

set_option maxHeartbeats 400000

namespace ShielddSecurity.GroupNativeSdk

open GroupByteCodec

/-- Global Jubjub Fq little-endian codec. This describes every native value and
canonical32-byte input, rather than the encoding of one desired witness.
The actual jubjub0.10/blst implementations remain independent source contracts. -/
structure FqBytes (Q : Type) where
  integer : Q → Nat
  bounded : ∀ value, integer value < Scalar.modulus
  bytes : Q → Bytes
  byteValue : ∀ value index,
    (bytes value index).val = littleEndianByte (integer value) index.val
  parse : Bytes → Option Q
  canonical : ∀ n : Nat, n < Scalar.modulus → ∀ bytes : Bytes,
    (∀ index, (bytes index).val = littleEndianByte n index.val) →
    ∃ value, parse bytes = some value ∧ integer value = n

/-- Canonical Jubjub Fr is a separate scalar field, with the smaller subgroup
order. Pari scalar(Fr) parses these same LE bytes as Fq before the BE reader. -/
structure FrBytes (R : Type) where
  integer : R → Nat
  bounded : ∀ value, integer value < Scalar.order
  bytes : R → Bytes
  byteValue : ∀ value index,
    (bytes value index).val = littleEndianByte (integer value) index.val

variable {F : Type} [Field F]

def readFq {Q : Type} (fq : FqBytes Q) (decoder : BERead (F := F)) (value : Q) : Option F :=
  decoder.decode (reverseBytes (fq.bytes value))

/-- Exact production pari.rs16-18 followed by circuits/encoding.rs10-17. -/
def readScalar {Q R : Type} (fq : FqBytes Q) (fr : FrBytes R)
    (decoder : BERead (F := F)) (value : R) : Option F :=
  match fq.parse (fr.bytes value) with
  | some embedded => readFq fq decoder embedded
  | none => none

theorem fq_read {Q : Type} (fq : FqBytes Q) (decoder : BERead (F := F)) (value : Q) :
    readFq fq decoder value = some (fq.integer value : F) :=
  reversed_coordinate_read decoder (fq.integer value) (fq.bounded value)
    (fq.bytes value) (fq.byteValue value)

theorem scalar_read {Q R : Type} (fq : FqBytes Q) (fr : FrBytes R)
    (decoder : BERead (F := F)) (value : R) :
    readScalar fq fr decoder value = some (fr.integer value : F) := by
  have bound : fr.integer value < Scalar.modulus :=
    lt_trans (fr.bounded value) (by decide : Scalar.order < Scalar.modulus)
  obtain ⟨embedded,parsed,integer⟩ := fq.canonical (fr.integer value) bound
    (fr.bytes value) (fr.byteValue value)
  simp only [readScalar,parsed,fq_read,integer]

theorem scalar_canonical [CharP F Scalar.modulus] {Q R : Type}
    (codec : TransferReduction.CanonicalField F) (fq : FqBytes Q) (fr : FrBytes R)
    (decoder : BERead (F := F)) (value : R) :
    readScalar fq fr decoder value = some (fr.integer value : F) ∧
      codec.decode (fr.integer value : F) = fr.integer value := by
  exact ⟨scalar_read fq fr decoder value,
    TransferReduction.decode_canonical_cast codec _
      (lt_trans (fr.bounded value) (by decide : Scalar.order < Scalar.modulus))⟩

/-- Functional native interfaces, interpreted in the standard FULL Jubjub
group. E represents SDK ExtendedPoint; S represents SDK SubgroupPoint. RedDSA
VerificationKey parsing itself permits torsion and identity, so K is not
assumed to be a subgroup or nonidentity type. Shieldd's compressed admission
gate below supplies those properties separately.

All operation/codec laws are global. randomizeBody and keyBytesBody describe
reddsa0.5.2 verification_key.rs128-138's concrete expression and cached bytes.
generatorParsed describes primitives/generators.rs10-16's scalar-one recipe.
coordinates describes primitives/lib.rs22-28's Extended→Affine u/v byte path.
No premise specifies a coordinate/scalar result for a particular RK witness. -/
structure Sdk {E S R K Q J : Type} [AddCommGroup J]
    (fq : FqBytes Q) (fr : FrBytes R) (d : F) (model : Group.StandardCurveModel J d) where
  embed : E → J
  promote : S → E
  add : E → E → E
  multiply : E → R → E
  addEmbedding : ∀ left right, embed (add left right) = embed left + embed right
  multiplyEmbedding : ∀ point scalar, embed (multiply point scalar) = fr.integer scalar • embed point
  spendAuth : E
  one : R
  oneInteger : fr.integer one = 1
  encode : E → Bytes
  encodingInjective : ∀ left right, encode left = encode right → embed left = embed right
  keyPoint : K → E
  keyBytes : K → Bytes
  keyBytesBody : ∀ key, keyBytes key = encode (keyPoint key)
  randomize : K → R → K
  randomizeBody : ∀ key scalar,
    keyPoint (randomize key scalar) = add (keyPoint key) (multiply spendAuth scalar)
  decodePoint : Bytes → Option S
  decodedEncoding : ∀ bytes point, decodePoint bytes = some point → encode (promote point) = bytes
  isIdentity : S → Bool
  identityReflects : ∀ point, isIdentity point = true ↔ embed (promote point) = 0
  subgroup : ∀ point, Scalar.order • embed (promote point) = 0
  generator : S
  generatorParsed : decodePoint (encode (multiply spendAuth one)) = some generator
  x : S → Q
  y : S → Q
  coordinates : ∀ point, model.coordinates (embed (promote point)) =
    ⟨(fq.integer (x point) : F),(fq.integer (y point) : F)⟩

variable {E S R K Q J : Type} [AddCommGroup J]
  {fq : FqBytes Q} {fr : FrBytes R} {d : F} {model : Group.StandardCurveModel J d}

/-- Exact encoding::point re-encoding check followed by encoding::nonidentity.
The native SubgroupPoint decoder is the explicit global functional boundary.
No success or subgroup condition is inferred from a RedDSA key type alone. -/
def admissionGate (sdk : Sdk (E := E) (S := S) (K := K) fq fr d model) (bytes : Bytes) : Option S :=
  match sdk.decodePoint bytes with
  | some point => if sdk.encode (sdk.promote point) = bytes then
      if sdk.isIdentity point then none else some point else none
  | none => none

def coordinateBytes [CharP F Scalar.modulus] (codec : TransferReduction.CanonicalField F)
    (sdk : Sdk (E := E) (S := S) (K := K) fq fr d model) :
    GroupNativeAuthorization.CoordinateBytes codec
      (fun point => model.coordinates (sdk.embed (sdk.promote point))) where
  x point := fq.bytes (sdk.x point)
  y point := fq.bytes (sdk.y point)
  xLittleEndian point index := by
    rw [sdk.coordinates]
    rw [TransferReduction.decode_canonical_cast codec _ (fq.bounded _)]
    exact fq.byteValue _ _
  yLittleEndian point index := by
    rw [sdk.coordinates]
    rw [TransferReduction.decode_canonical_cast codec _ (fq.bounded _)]
    exact fq.byteValue _ _

theorem native_point_read [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (decoder : BERead (F := F))
    (sdk : Sdk (E := E) (S := S) (K := K) fq fr d model) (point : S) :
    GroupNativeAuthorization.readPoint decoder (fq.bytes (sdk.x point)) (fq.bytes (sdk.y point)) =
      some (model.coordinates (sdk.embed (sdk.promote point))) :=
  GroupNativeAuthorization.read_point_coordinates codec decoder _ (coordinateBytes codec sdk) point

theorem admission (sdk : Sdk (E := E) (S := S) (K := K) fq fr d model) (bytes : Bytes) (point : S)
    (accepted : admissionGate sdk bytes = some point) :
    sdk.encode (sdk.promote point) = bytes ∧
      Scalar.order • sdk.embed (sdk.promote point) = 0 ∧ sdk.embed (sdk.promote point) ≠ 0 := by
  unfold admissionGate at accepted
  cases parsed : sdk.decodePoint bytes with
  | none => simp only [parsed] at accepted; cases accepted
  | some decoded =>
      simp only [parsed] at accepted
      split at accepted
      next encoded =>
        split at accepted
        next identity => cases accepted
        next nonidentity =>
          cases Option.some.inj accepted
          exact ⟨encoded,sdk.subgroup _,fun zero => nonidentity ((sdk.identityReflects _).mpr zero)⟩
      next noncanonical => cases accepted

theorem admitted_key (sdk : Sdk (E := E) (S := S) (K := K) fq fr d model) (key : K) (point : S)
    (accepted : admissionGate sdk (sdk.keyBytes key) = some point) :
    sdk.embed (sdk.promote point) = sdk.embed (sdk.keyPoint key) ∧
      Scalar.order • sdk.embed (sdk.keyPoint key) = 0 ∧ sdk.embed (sdk.keyPoint key) ≠ 0 := by
  have legal := admission sdk _ point accepted
  have same := sdk.encodingInjective (sdk.promote point) (sdk.keyPoint key)
    (legal.1.trans (sdk.keyBytesBody key))
  exact ⟨same,same ▸ legal.2.1,same ▸ legal.2.2⟩

theorem generator_embedding (sdk : Sdk (E := E) (S := S) (K := K) fq fr d model) :
    sdk.embed (sdk.promote sdk.generator) = sdk.embed sdk.spendAuth := by
  have same := sdk.encodingInjective (sdk.promote sdk.generator) (sdk.multiply sdk.spendAuth sdk.one)
    (sdk.decodedEncoding _ _ sdk.generatorParsed)
  rw [sdk.multiplyEmbedding,sdk.oneInteger,one_nsmul] at same
  exact same

theorem randomize_embedding (sdk : Sdk (E := E) (S := S) (K := K) fq fr d model) (key : K) (scalar : R) :
    sdk.embed (sdk.keyPoint (sdk.randomize key scalar)) =
      sdk.embed (sdk.keyPoint key) + fr.integer scalar • sdk.embed (sdk.promote sdk.generator) := by
  rw [sdk.randomizeBody,sdk.addEmbedding,sdk.multiplyEmbedding,generator_embedding]

theorem randomized_admission (sdk : Sdk (E := E) (S := S) (K := K) fq fr d model) (key : K) (scalar : R) (point : S)
    (accepted : admissionGate sdk (sdk.keyBytes (sdk.randomize key scalar)) = some point) :
    sdk.embed (sdk.promote point) =
      sdk.embed (sdk.keyPoint key) + fr.integer scalar • sdk.embed (sdk.promote sdk.generator) ∧
    Scalar.order • sdk.embed (sdk.promote point) = 0 ∧ sdk.embed (sdk.promote point) ≠ 0 := by
  have same := admitted_key sdk (sdk.randomize key scalar) point accepted
  exact ⟨same.1.trans (randomize_embedding sdk key scalar),
    (admission sdk _ point accepted).2⟩

/-- Production key.randomize agrees with the circuit native operation AFTER
both compressed admissions and actual coordinate reads. The generator is the
SDK's scalar-one-derived SPEND_AUTH. Neither output coordinates nor a scalar
conversion result are premises; both are derived from global functional laws.
Pinned source contracts for the SDK operations and FFI codecs remain explicit. -/
theorem randomized_native_authorization [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (writer : BEWrite codec)
    (decoder : BERead (F := F)) (sdk : Sdk (E := E) (S := S) (K := K) fq fr d model)
    (imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary*imaginary = -1) (two : (2 : F) ≠ 0)
    (key : K) (scalar : R) (keyPoint randomizedPoint : S)
    (keyAdmission : admissionGate sdk (sdk.keyBytes key) = some keyPoint)
    (randomizedAdmission : admissionGate sdk (sdk.keyBytes (sdk.randomize key scalar)) = some randomizedPoint) :
    readScalar fq fr decoder scalar = some (fr.integer scalar : F) ∧
      GroupNativeAuthorization.readAuthorization decoder writer d
        (fq.bytes (sdk.x keyPoint)) (fq.bytes (sdk.y keyPoint))
        (fq.bytes (sdk.x sdk.generator)) (fq.bytes (sdk.y sdk.generator))
        (fr.integer scalar : F) =
        some (model.coordinates (sdk.embed (sdk.promote randomizedPoint))) := by
  have input := admitted_key sdk key keyPoint keyAdmission
  have output := randomized_admission sdk key scalar randomizedPoint randomizedAdmission
  have native := GroupNativeAuthorization.read_authorization_coordinates codec writer decoder
    d imaginary model (fun point => sdk.embed (sdk.promote point)) (coordinateBytes codec sdk)
    nonSquare imaginarySquare two keyPoint sdk.generator (fr.integer scalar : F)
  rw [TransferReduction.decode_canonical_cast codec _
    (lt_trans (fr.bounded scalar) (by decide : Scalar.order < Scalar.modulus)),
    input.1,← output.1] at native
  exact ⟨scalar_read fq fr decoder scalar,native⟩

set_option pp.all true in
#check @fq_read
#print axioms fq_read
set_option pp.all true in
#check @scalar_read
#print axioms scalar_read
set_option pp.all true in
#check @scalar_canonical
#print axioms scalar_canonical
set_option pp.all true in
#check @native_point_read
#print axioms native_point_read
set_option pp.all true in
#check @admission
#print axioms admission
set_option pp.all true in
#check @admitted_key
#print axioms admitted_key
set_option pp.all true in
#check @generator_embedding
#print axioms generator_embedding
set_option pp.all true in
#check @randomize_embedding
#print axioms randomize_embedding
set_option pp.all true in
#check @randomized_admission
#print axioms randomized_admission
set_option pp.all true in
#check @randomized_native_authorization
#print axioms randomized_native_authorization

end ShielddSecurity.GroupNativeSdk
