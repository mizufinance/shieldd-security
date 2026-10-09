import ShielddSecurity.ShielddNativeSdk

set_option maxHeartbeats 250000

namespace ShielddSecurity.TransferNativeSignatureWrapper

variable {F : Type} [Field F]
  {E S R K Q Signing J Message Signature : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

/-! Owned keys::ensure_nonidentity_spend_auth_key followed by
note_reshape::verify_auth_sig. Upstream group/byte operations are the existing
named global functional interface; the primitive signature verifier is kept
separate. This exact wrapper never changes the native key, message or signature.
No cryptographic success probability, ownership or secret possession follows
from the primitive verification Bool without a separate signature-game bound. -/

def verifyAuth (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (verify : K → Message → Signature → Bool) (key : K) (message : Message)
    (signature : Signature) : Option Unit :=
  match ShielddNativeSdk.nonidentity upstream (upstream.keyBytes key) with
  | none => none
  | some _ => if verify key message signature then some () else none

theorem wrapper_success
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (verify : K → Message → Signature → Bool) (key : K) (message : Message)
    (signature : Signature) (success : verifyAuth upstream verify key message signature = some ()) :
    ∃ point, ShielddNativeSdk.nonidentity upstream (upstream.keyBytes key) = some point ∧
      upstream.encode (upstream.promote point) = upstream.keyBytes key ∧
      upstream.embed (upstream.promote point) = upstream.embed (upstream.keyPoint key) ∧
      Scalar.order • upstream.embed (upstream.keyPoint key) = 0 ∧
      upstream.embed (upstream.keyPoint key) ≠ 0 ∧ verify key message signature = true := by
  cases accepted : ShielddNativeSdk.nonidentity upstream (upstream.keyBytes key) with
  | none => simp only [verifyAuth, accepted] at success; cases success
  | some point =>
      have verified : verify key message signature = true := by
        cases result : verify key message signature with
        | false => simp only [verifyAuth, accepted, result, Bool.false_eq_true, if_false] at success
                   cases success
        | true => rfl
      have admission := GroupNativeSdk.admission (ShielddNativeSdk.sdk upstream) _ point accepted
      have keyAdmission := GroupNativeSdk.admitted_key (ShielddNativeSdk.sdk upstream) key point accepted
      exact ⟨point, rfl, admission.1, keyAdmission.1, keyAdmission.2.1,
        keyAdmission.2.2, verified⟩

theorem identity_key_refused
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (verify : K → Message → Signature → Bool) (key : K) (message : Message)
    (signature : Signature) (identity : upstream.embed (upstream.keyPoint key) = 0) :
    verifyAuth upstream verify key message signature ≠ some () := by
  intro success
  obtain ⟨point, accepted, encoded, same, subgroup, nonidentity, verified⟩ :=
    wrapper_success upstream verify key message signature success
  exact nonidentity identity

theorem accepted_key_coordinate_reader [CharP F Scalar.modulus] {Encoded Native : Type}
    (codec : TransferReduction.CanonicalField F)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (verify : K → Message → Signature → Bool) (key : K) (message : Message)
    (signature : Signature) (success : verifyAuth upstream verify key message signature = some ()) :
    ShielddNativeSdk.key backend upstream key =
      some (model.coordinates (upstream.embed (upstream.keyPoint key))) ∧
      verify key message signature = true := by
  obtain ⟨point, accepted, encoded, same, subgroup, nonidentity, verified⟩ :=
    wrapper_success upstream verify key message signature success
  exact ⟨ShielddNativeSdk.key_read codec backend upstream key point accepted, verified⟩

theorem randomized_key_argument
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (verify : K → Message → Signature → Bool) (ak : K) (randomizer : R)
    (message : Message) (signature : Signature)
    (success : verifyAuth upstream verify (ShielddNativeSdk.planRk upstream ak randomizer)
      message signature = some ()) :
    upstream.embed (upstream.keyPoint (ShielddNativeSdk.planRk upstream ak randomizer)) =
      upstream.embed (upstream.keyPoint ak) +
        fr.integer randomizer • upstream.embed (upstream.promote upstream.spendAuthSubgroup) ∧
    upstream.embed (upstream.keyPoint (ShielddNativeSdk.planRk upstream ak randomizer)) ≠ 0 ∧
    verify (ShielddNativeSdk.planRk upstream ak randomizer) message signature = true := by
  obtain ⟨point, accepted, encoded, same, subgroup, nonidentity, verified⟩ :=
    wrapper_success upstream verify _ message signature success
  exact ⟨ShielddNativeSdk.plan_randomization upstream ak randomizer, nonidentity, verified⟩

set_option pp.all true in
#check @wrapper_success
#print axioms wrapper_success
set_option pp.all true in
#check @identity_key_refused
#print axioms identity_key_refused
set_option pp.all true in
#check @accepted_key_coordinate_reader
#print axioms accepted_key_coordinate_reader
set_option pp.all true in
#check @randomized_key_argument
#print axioms randomized_key_argument

end ShielddSecurity.TransferNativeSignatureWrapper
