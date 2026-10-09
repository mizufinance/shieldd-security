import ShielddSecurity.ShielddViewingKeySeed
import ShielddSecurity.ShielddNativeSdk

set_option maxHeartbeats 250000

namespace ShielddSecurity.ShielddViewingKeyCoordinates

variable {F : Type} [Field F]
variable {E S R K Q Signing J : Type} [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (d : F) (model : Group.StandardCurveModel J d)
variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)

/-- The SDK FullViewingKey parser uses AK cached compressed bytes, parses a
SubgroupPoint, then promotes that parsed point for affine coordinate extraction.
The global upstream cache and codec laws identify its group element with AK;
no coordinate for this particular key is supplied as a premise. -/
theorem decoded_key_embedding (key : K) (point : S)
    (parsed : upstream.decodePoint (upstream.keyBytes key) = some point) :
    upstream.embed (upstream.promote point) = upstream.embed (upstream.keyPoint key) := by
  have bytes := upstream.decodedEncoding _ _ parsed
  rw [upstream.keyBytesBody] at bytes
  exact upstream.encodingInjective _ _ bytes

/-- Defined source input extraction: NK and the u/v values of the SDK's
parsed SubgroupPoint. The owned pari coordinate reader is part of the seed. -/
def seed {Encoded Native : Type} (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (nk : Q) (point : S) (base : Nat → F) : Nat → F :=
  ShielddViewingKeySeed.seed fq backend nk
    (upstream.affine (upstream.promote point)).1 (upstream.affine (upstream.promote point)).2 base

theorem seeded_key_coordinates {Encoded Native : Type}
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (nk : Q) (key : K) (point : S) (base : Nat → F)
    (parsed : upstream.decodePoint (upstream.keyBytes key) = some point) :
    (⟨seed fq fr d model upstream backend nk point base 1980,
      seed fq fr d model upstream backend nk point base 1981⟩ : Group.Point F) =
      model.coordinates (upstream.embed (upstream.keyPoint key)) := by
  rw [← decoded_key_embedding fq fr d model upstream key point parsed,
    upstream.affineMeaning]
  simp [seed,ShielddViewingKeySeed.seed,ShielddViewingKeySeed.columns,
    ShielddViewingKeySeed.values,patchAssignment,ShielddViewingKeySeed.read_value,
    ShielddNativeIvkHash.fqValue]

/-- Actual SDK nonzero-IVK admission after the defined compressed-key/affine
input path. This derives circuit hash/reduction legality for the same seeded
NK/AK columns; it does not assume those columns' desired values or row truth. -/
theorem seeded_hash_legal [CharP F Scalar.modulus] {Encoded Native : Type}
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
    (primitives : ShielddViewingKeyAdmission.Primitives fq fr)
    (codec : TransferReduction.CanonicalField F) (parameters : Poseidon.Parameters F 6)
    (nk : Q) (point : S) (scalar : R) (base : Nat → F)
    (accepted : ShielddViewingKeyAdmission.incomingScalar primitives
      (ShielddNativeIvkSource.sdkIvk fq arithmetic initial codec parameters nk
        (upstream.affine (upstream.promote point)).1 (upstream.affine (upstream.promote point)).2) = some scalar) :
    codec.decode (Poseidon.hash6 parameters 16
      (ShielddViewingKeySeed.hashInputs.map (eval (seed fq fr d model upstream backend nk point base)))) %
        Scalar.order ≠ 0 :=
  ShielddViewingKeySeed.seeded_hash_legal fq fr arithmetic initial primitives backend codec parameters nk
    (upstream.affine (upstream.promote point)).1 (upstream.affine (upstream.promote point)).2 scalar base accepted

set_option pp.all true in
#check @decoded_key_embedding
#print axioms decoded_key_embedding
set_option pp.all true in
#check @seeded_key_coordinates
#print axioms seeded_key_coordinates
set_option pp.all true in
#check @seeded_hash_legal
#print axioms seeded_hash_legal

end ShielddSecurity.ShielddViewingKeyCoordinates
