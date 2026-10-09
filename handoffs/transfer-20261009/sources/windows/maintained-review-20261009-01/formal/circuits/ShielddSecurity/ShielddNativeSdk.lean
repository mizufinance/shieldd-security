import ShielddSecurity.GroupNativeSdk
import ShielddSecurity.ShielddScalarReader

set_option maxHeartbeats 400000

namespace ShielddSecurity.ShielddNativeSdk

open GroupByteCodec

variable {F : Type} [Field F]

/-- Exact named upstream operations, globally interpreted in full Jubjub.
This contract excludes Shieldd's coordinate reader, scalar adapter, admission
branch, SPEND_AUTH constructor, and production randomization wrapper. Those
are defined below and their laws are proved from these upstream operations.
All quantifiers cover the native types, not one chosen Transfer witness. -/
structure Upstream (E S R K Q Signing J : Type) [AddCommGroup J]
    (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
    (d : F) (model : Group.StandardCurveModel J d) where
  embed : E → J
  promote : S → E
  add : E → E → E
  multiply : E → R → E
  addEmbedding : ∀ left right, embed (add left right) = embed left + embed right
  multiplyEmbedding : ∀ point scalar, embed (multiply point scalar) = fr.integer scalar • embed point
  spendAuth : E
  spendAuthSubgroup : S
  spendAuthEmbedding : embed (promote spendAuthSubgroup) = embed spendAuth
  one : R
  oneInteger : fr.integer one = 1
  encode : E → Bytes
  encodingInjective : ∀ left right, encode left = encode right → embed left = embed right
  encodingCoherent : ∀ left right, embed left = embed right → encode left = encode right
  keyPoint : K → E
  keyBytes : K → Bytes
  keyBytesBody : ∀ key, keyBytes key = encode (keyPoint key)
  randomize : K → R → K
  randomizeBody : ∀ key scalar,
    keyPoint (randomize key scalar) = add (keyPoint key) (multiply spendAuth scalar)
  decodePoint : Bytes → Option S
  decodedEncoding : ∀ bytes point, decodePoint bytes = some point → encode (promote point) = bytes
  decodeEncode : ∀ point, decodePoint (encode (promote point)) = some point
  isIdentity : S → Bool
  identityReflects : ∀ point, isIdentity point = true ↔ embed (promote point) = 0
  subgroup : ∀ point, Scalar.order • embed (promote point) = 0
  affine : E → Q × Q
  affineMeaning : ∀ point, model.coordinates (embed point) =
    ⟨(fq.integer (affine point).1 : F),(fq.integer (affine point).2 : F)⟩
  signing : R → Signing
  parseSigning : Bytes → Option Signing
  signingCanonical : ∀ scalar, parseSigning (fr.bytes scalar) = some (signing scalar)
  verification : Signing → K
  verificationEmbedding : ∀ scalar,
    embed (keyPoint (verification (signing scalar))) = fr.integer scalar • embed spendAuth

/-- primitives/generators.rs writes exactly one into the first LE byte. -/
def oneBytes : Bytes := fun index => ⟨if index.val = 0 then 1 else 0, by split <;> decide⟩

private theorem one_byte_value (index : Fin 32) :
    (oneBytes index).val = littleEndianByte 1 index.val := by
  by_cases zero : index.val = 0
  · simp [oneBytes,littleEndianByte,zero]
  · have positive : 1 < (2 : Nat)^(8*index.val) := one_lt_pow' (by decide) (by omega)
    simp [oneBytes,littleEndianByte,zero,Nat.div_eq_of_lt positive]

variable {E S R K Q Signing J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

theorem scalar_one_bytes (upstream : Upstream E S R K Q Signing J fq fr d model) :
    fr.bytes upstream.one = oneBytes := by
  funext index
  apply Fin.ext
  rw [fr.byteValue,upstream.oneInteger]
  exact (one_byte_value index).symm

/-- The actual source SPEND_AUTH call sequence, including both fallible
upstream parsers. It is not defined as an assumed desired subgroup point. -/
def spendAuthProgram (upstream : Upstream E S R K Q Signing J fq fr d model) : Option S :=
  match upstream.parseSigning oneBytes with
  | some signing => upstream.decodePoint (upstream.keyBytes (upstream.verification signing))
  | none => none

theorem spend_auth_program (upstream : Upstream E S R K Q Signing J fq fr d model) :
    spendAuthProgram upstream = some upstream.spendAuthSubgroup := by
  have parsed : upstream.parseSigning oneBytes = some (upstream.signing upstream.one) := by
    rw [← scalar_one_bytes upstream]
    exact upstream.signingCanonical upstream.one
  have keyEmbedding := upstream.verificationEmbedding upstream.one
  rw [upstream.oneInteger,one_nsmul] at keyEmbedding
  have canonical : upstream.keyBytes (upstream.verification (upstream.signing upstream.one)) =
      upstream.encode (upstream.promote upstream.spendAuthSubgroup) := by
    rw [upstream.keyBytesBody]
    exact upstream.encodingCoherent _ _ (keyEmbedding.trans upstream.spendAuthEmbedding.symm)
  simp only [spendAuthProgram,parsed,canonical,upstream.decodeEncode]

theorem generator_parsed (upstream : Upstream E S R K Q Signing J fq fr d model) :
    upstream.decodePoint (upstream.encode (upstream.multiply upstream.spendAuth upstream.one)) =
      some upstream.spendAuthSubgroup := by
  have multiplication := upstream.multiplyEmbedding upstream.spendAuth upstream.one
  rw [upstream.oneInteger,one_nsmul] at multiplication
  have encoded := upstream.encodingCoherent _ _ (multiplication.trans upstream.spendAuthEmbedding.symm)
  rw [encoded]
  exact upstream.decodeEncode upstream.spendAuthSubgroup

/-- primitives::coordinates converts Extended to Affine, then chooses u/v.
The Affine backend law is upstream; the two owned selections are definitions. -/
def coordinateX (upstream : Upstream E S R K Q Signing J fq fr d model) (point : S) : Q :=
  (upstream.affine (upstream.promote point)).1
def coordinateY (upstream : Upstream E S R K Q Signing J fq fr d model) (point : S) : Q :=
  (upstream.affine (upstream.promote point)).2

/-- Build the legacy theorem interface from the exact source programs. Owned
generator/coordinate bodies are proved above, rather than supplied as fields. -/
def sdk (upstream : Upstream E S R K Q Signing J fq fr d model) :
    GroupNativeSdk.Sdk (E := E) (S := S) (K := K) fq fr d model where
  embed := upstream.embed
  promote := upstream.promote
  add := upstream.add
  multiply := upstream.multiply
  addEmbedding := upstream.addEmbedding
  multiplyEmbedding := upstream.multiplyEmbedding
  spendAuth := upstream.spendAuth
  one := upstream.one
  oneInteger := upstream.oneInteger
  encode := upstream.encode
  encodingInjective := upstream.encodingInjective
  keyPoint := upstream.keyPoint
  keyBytes := upstream.keyBytes
  keyBytesBody := upstream.keyBytesBody
  randomize := upstream.randomize
  randomizeBody := upstream.randomizeBody
  decodePoint := upstream.decodePoint
  decodedEncoding := upstream.decodedEncoding
  isIdentity := upstream.isIdentity
  identityReflects := upstream.identityReflects
  subgroup := upstream.subgroup
  generator := upstream.spendAuthSubgroup
  generatorParsed := generator_parsed upstream
  x := coordinateX upstream
  y := coordinateY upstream
  coordinates := fun point => upstream.affineMeaning (upstream.promote point)

/-- Owned encoding::field and native_point share the same reverse+AllowZero
reader. The backend decoder is the constructed ShielddScalarReader instance. -/
def field {Encoded Native : Type} (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (value : Q) : Option F :=
  (ShielddScalarReader.decoder backend).decode (reverseBytes (fq.bytes value))

def nativePoint {Encoded Native : Type} (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (upstream : Upstream E S R K Q Signing J fq fr d model) (point : S) : Option (Group.Point F) :=
  GroupNativeAuthorization.readPoint (ShielddScalarReader.decoder backend)
    (fq.bytes (coordinateX upstream point)) (fq.bytes (coordinateY upstream point))

def scalar {Encoded Native : Type} (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (value : R) : Option F :=
  match fq.parse (fr.bytes value) with
  | some embedded => field (fq := fq) backend embedded
  | none => none

/-- Exact owned point/nonidentity guards, separate from RedDSA's key type. -/
def nonidentity (upstream : Upstream E S R K Q Signing J fq fr d model) (bytes : Bytes) : Option S :=
  match upstream.decodePoint bytes with
  | some point => if upstream.encode (upstream.promote point) = bytes then
      if upstream.isIdentity point then none else some point else none
  | none => none

def key {Encoded Native : Type} (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (upstream : Upstream E S R K Q Signing J fq fr d model) (verification : K) : Option (Group.Point F) :=
  match nonidentity upstream (upstream.keyBytes verification) with
  | some point => nativePoint backend upstream point
  | none => none

/-- transfer::plan::rk applies the exact upstream randomize operation. -/
def planRk (upstream : Upstream E S R K Q Signing J fq fr d model) (verification : K) (randomizer : R) : K :=
  upstream.randomize verification randomizer

theorem field_read {Encoded Native : Type} (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (value : Q) : field (fq := fq) backend value = some (fq.integer value : F) :=
  GroupNativeSdk.fq_read fq (ShielddScalarReader.decoder backend) value

theorem scalar_read {Encoded Native : Type} (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (value : R) : scalar (fq := fq) (fr := fr) backend value = some (fr.integer value : F) :=
  GroupNativeSdk.scalar_read fq fr (ShielddScalarReader.decoder backend) value

theorem native_point_read [CharP F Scalar.modulus] {Encoded Native : Type}
    (codec : TransferReduction.CanonicalField F) (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (upstream : Upstream E S R K Q Signing J fq fr d model) (point : S) :
    nativePoint backend upstream point = some (model.coordinates (upstream.embed (upstream.promote point))) :=
  GroupNativeSdk.native_point_read codec (ShielddScalarReader.decoder backend) (sdk upstream) point

theorem admission_program (upstream : Upstream E S R K Q Signing J fq fr d model) (bytes : Bytes) :
    nonidentity upstream bytes = GroupNativeSdk.admissionGate (sdk upstream) bytes := rfl

theorem key_read [CharP F Scalar.modulus] {Encoded Native : Type}
    (codec : TransferReduction.CanonicalField F) (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (upstream : Upstream E S R K Q Signing J fq fr d model) (verification : K) (point : S)
    (accepted : nonidentity upstream (upstream.keyBytes verification) = some point) :
    key backend upstream verification = some (model.coordinates (upstream.embed (upstream.keyPoint verification))) := by
  have legal := GroupNativeSdk.admitted_key (sdk upstream) verification point accepted
  have same : upstream.embed (upstream.promote point) = upstream.embed (upstream.keyPoint verification) := legal.1
  simp only [key,accepted]
  rw [native_point_read codec backend upstream point]
  exact congrArg some (congrArg model.coordinates same)

theorem plan_randomization (upstream : Upstream E S R K Q Signing J fq fr d model)
    (verification : K) (randomizer : R) :
    upstream.embed (upstream.keyPoint (planRk upstream verification randomizer)) =
      upstream.embed (upstream.keyPoint verification) +
        fr.integer randomizer • upstream.embed (upstream.promote upstream.spendAuthSubgroup) :=
  GroupNativeSdk.randomize_embedding (sdk upstream) verification randomizer

set_option pp.all true in
#check @scalar_one_bytes
#print axioms scalar_one_bytes
set_option pp.all true in
#check @spend_auth_program
#print axioms spend_auth_program
set_option pp.all true in
#check @generator_parsed
#print axioms generator_parsed
set_option pp.all true in
#check @field_read
#print axioms field_read
set_option pp.all true in
#check @scalar_read
#print axioms scalar_read
set_option pp.all true in
#check @native_point_read
#print axioms native_point_read
set_option pp.all true in
#check @admission_program
#print axioms admission_program
set_option pp.all true in
#check @key_read
#print axioms key_read
set_option pp.all true in
#check @plan_randomization
#print axioms plan_randomization

end ShielddSecurity.ShielddNativeSdk
