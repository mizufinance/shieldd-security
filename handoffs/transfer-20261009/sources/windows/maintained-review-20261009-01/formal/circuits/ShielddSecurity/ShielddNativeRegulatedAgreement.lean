import ShielddSecurity.ShielddNativeAddress

set_option maxHeartbeats 200000

namespace ShielddSecurity.ShielddNativeRegulatedAgreement

open ShielddNativeAddress GroupByteCodec

variable {F : Type} [Field F]
  {E S R K Q Signing J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

/-- IncomingViewingKey::key_agreement_with_element first constructs Public,
then ka::Secret parses its stored canonical Fr bytes, multiplies that exact
point, and returns its canonical encoding. Invalid secret bytes totalize the
native unwrap failure as None; a successful fromScalar constructor eliminates
that case. The shared point's nonidentity check is a separate caller step. -/
def agreement
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream) (secret : Secret) (input : S) : Option Bytes := do
  let publicKey ← publicFromPoint upstream input
  let scalar ← primitives.parseFr secret.bytes
  pure (upstream.encode (upstream.promote (primitives.multiply publicKey.point scalar)))

theorem agreement_result
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream) (guards : ShielddViewingKeyAdmission.Primitives fq fr)
    (scalar : R) (secret : Secret) (input : S) (bytes : Bytes)
    (constructed : fromScalar guards scalar = some secret)
    (agreed : agreement upstream primitives secret input = some bytes) :
    upstream.isIdentity input = false ∧
      bytes = upstream.encode (upstream.promote (primitives.multiply input scalar)) := by
  have parsed := secret_parse upstream primitives guards scalar secret constructed
  cases identity : upstream.isIdentity input with
  | true => simp [agreement,publicFromPoint,identity] at agreed
  | false =>
    have same : upstream.encode (upstream.promote (primitives.multiply input scalar)) = bytes :=
      Option.some.inj (by simpa [agreement,publicFromPoint,identity,parsed] using agreed)
    exact ⟨rfl,same.symm⟩

theorem shared_result
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream) (guards : ShielddViewingKeyAdmission.Primitives fq fr)
    (scalar : R) (secret : Secret) (input shared : S) (bytes : Bytes)
    (constructed : fromScalar guards scalar = some secret)
    (agreed : agreement upstream primitives secret input = some bytes)
    (decoded : ShielddNativeSdk.nonidentity upstream bytes = some shared) :
    shared = primitives.multiply input scalar := by
  obtain ⟨_,same⟩ := agreement_result upstream primitives guards scalar secret input bytes constructed agreed
  rw [same] at decoded
  cases identity : upstream.isIdentity (primitives.multiply input scalar) with
  | true => simp [ShielddNativeSdk.nonidentity, upstream.decodeEncode, identity] at decoded
  | false =>
    have samePoint : primitives.multiply input scalar = shared :=
      Option.some.inj (by
        simpa [ShielddNativeSdk.nonidentity, upstream.decodeEncode, identity] using decoded)
    exact samePoint.symm

theorem shared_coordinates
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream) (guards : ShielddViewingKeyAdmission.Primitives fq fr)
    (scalar : R) (secret : Secret) (input shared : S) (bytes : Bytes)
    (constructed : fromScalar guards scalar = some secret)
    (agreed : agreement upstream primitives secret input = some bytes)
    (decoded : ShielddNativeSdk.nonidentity upstream bytes = some shared) :
    model.coordinates (upstream.embed (upstream.promote shared)) =
      model.coordinates (fr.integer scalar • upstream.embed (upstream.promote input)) := by
  rw [shared_result upstream primitives guards scalar secret input shared bytes constructed agreed decoded,
    primitives.promoteMultiply,upstream.multiplyEmbedding]

set_option pp.all true in
#check @agreement_result
#print axioms agreement_result
set_option pp.all true in
#check @shared_result
#print axioms shared_result
set_option pp.all true in
#check @shared_coordinates
#print axioms shared_coordinates

end ShielddSecurity.ShielddNativeRegulatedAgreement
