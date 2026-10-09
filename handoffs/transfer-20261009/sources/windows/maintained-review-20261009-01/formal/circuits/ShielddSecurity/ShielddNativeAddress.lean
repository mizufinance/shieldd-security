import ShielddSecurity.ShielddNativeSdk
import ShielddSecurity.ShielddViewingKeyAdmission

set_option maxHeartbeats 300000

namespace ShielddSecurity.ShielddNativeAddress

open GroupByteCodec

abbrev ShortBytes := Fin 16 → Byte
abbrev WideBytes := Fin 64 → Byte

structure Index where
  account : Fin (2^32)
  randomizer : Fin 12 → Byte

/-- AddressIndex::to_bytes: four LE account bytes, then the twelve unchanged
randomizer bytes. Copying these arrays introduces no new arithmetic premise. -/
def indexBytes (index : Index) : ShortBytes := fun position =>
  if low : position.val < 4 then
    ⟨index.account.val / 2^(8*position.val) % 256, Nat.mod_lt _ (by decide)⟩
  else index.randomizer ⟨position.val-4,by omega⟩

variable {F : Type} [Field F]
  {E S R K Q Signing J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

/-- Exact global native primitives, independently of one wallet/address.
The only mathematical laws are the upstream canonical Fr parser and subgroup
multiplication's promotion into the already named Extended operation. AES,
BLAKE2b, Fq-wide and SDK map callbacks are unrestricted total functions here;
no hash security, desired generator, nonidentity or address output is presumed.
Instantiating these callbacks with the pinned native functions remains an
explicit source correspondence obligation. The owned wrappers below perform
their actual composition and guards. -/
structure Primitives (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model) where
  parseFr : Bytes → Option R
  parseCanonical : ∀ scalar, parseFr (fr.bytes scalar) = some scalar
  multiply : S → R → S
  promoteMultiply : ∀ point scalar,
    upstream.promote (multiply point scalar) = upstream.multiply (upstream.promote point) scalar
  aes128 : ShortBytes → ShortBytes → ShortBytes
  blake2b : List Byte → ShortBytes → WideBytes
  fqFromWide : WideBytes → Q
  toSubgroup : Q → S

structure Secret where
  bytes : Bytes

structure Public (S : Type) where
  point : S
  deriving DecidableEq

structure Address (S : Type) where
  diversifier : ShortBytes
  diversified : S
  transmission : Public S

def fromScalar (guards : ShielddViewingKeyAdmission.Primitives fq fr) (scalar : R) : Option Secret :=
  if guards.zeroCheck scalar then none else some ⟨fr.bytes scalar⟩

/-- DiversifierKey::diversifier_for_index copies key/index bytes into AES128,
encrypts one block and copies the ciphertext into the diversifier. -/
def diversifierForIndex
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream) (key : ShortBytes) (index : Index) : ShortBytes :=
  primitives.aes128 key (indexBytes index)

def personalization : List Byte := [83,104,105,101,108,100,100,95,68,105,118,114,115,102,121]

/-- Diversifier::diversified_generator uses the exact Shieldd_Divrsfy personal
BLAKE2b digest, Fq::from_bytes_wide, then the SDK map::to_subgroup callback. -/
def diversifiedGenerator
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream) (diversifier : ShortBytes) : S :=
  primitives.toSubgroup (primitives.fqFromWide (primitives.blake2b personalization diversifier))

def publicFromPoint
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model) (point : S) : Option (Public S) :=
  if upstream.isIdentity point then none else some ⟨point⟩

/-- ka::Secret::scalar parses its stored LE bytes. The source unwrap is
represented by the successful branch; failed parsing cannot fabricate a key. -/
def diversifiedPublic
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream) (secret : Secret) (generator : S) : Option (Public S) :=
  match primitives.parseFr secret.bytes with
  | some scalar => publicFromPoint upstream (primitives.multiply generator scalar)
  | none => none

/-- Address::from_components recomputes the same diversified generator and
rejects its identity. Public's separate constructor has already guarded its
point. A successful object retains exactly these three fields. -/
def fromComponents
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream) (diversifier : ShortBytes) (key : Public S) : Option (Address S) :=
  let generator := diversifiedGenerator upstream primitives diversifier
  if upstream.isIdentity generator then none else some ⟨diversifier,generator,key⟩

def paymentAddress
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream) (secret : Secret) (key : ShortBytes) (index : Index) : Option (Address S) :=
  let diversifier := diversifierForIndex upstream primitives key index
  let generator := diversifiedGenerator upstream primitives diversifier
  match diversifiedPublic upstream primitives secret generator with
  | some publicKey => fromComponents upstream primitives diversifier publicKey
  | none => none

/-- IncomingViewingKey::views_address is the actual successful native public
construction followed by Public's derived point equality. It does not take a
desired coordinate/scalar/row equality as an input. -/
def viewsAddress [DecidableEq S]
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream) (secret : Secret) (address : Address S) : Bool :=
  match diversifiedPublic upstream primitives secret address.diversified with
  | some key => decide (key = address.transmission)
  | none => false

theorem secret_parse
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream) (guards : ShielddViewingKeyAdmission.Primitives fq fr)
    (scalar : R) (secret : Secret) (accepted : fromScalar guards scalar = some secret) :
    primitives.parseFr secret.bytes = some scalar := by
  cases zero : guards.zeroCheck scalar with
  | true => simp only [fromScalar,zero,ite_true] at accepted; cases accepted
  | false =>
      have same : (⟨fr.bytes scalar⟩ : Secret) = secret :=
        Option.some.inj (by simpa only [fromScalar,zero,Bool.false_eq_true,ite_false] using accepted)
      rw [← same]
      exact primitives.parseCanonical scalar

/-- FullViewingKey::incoming's successful reduced-scalar guard discharges the
subsequent ka::Secret::from_scalar zero guard on that same native scalar. -/
theorem secret_from_ivk (guards : ShielddViewingKeyAdmission.Primitives fq fr)
    (hash : Q) (scalar : R)
    (accepted : ShielddViewingKeyAdmission.incomingScalar guards hash = some scalar) :
    fromScalar guards scalar = some ⟨fr.bytes scalar⟩ := by
  have positive := (ShielddViewingKeyAdmission.successful_scalar guards hash scalar accepted).2.1
  cases zero : guards.zeroCheck scalar with
  | false => simp only [fromScalar,zero,Bool.false_eq_true,ite_false]
  | true =>
      have value := (guards.zeroMeaning scalar).mp zero
      omega

theorem diversified_public_relation
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream) (guards : ShielddViewingKeyAdmission.Primitives fq fr)
    (scalar : R) (secret : Secret) (generator : S) (key : Public S)
    (accepted : fromScalar guards scalar = some secret)
    (constructed : diversifiedPublic upstream primitives secret generator = some key) :
    key.point = primitives.multiply generator scalar := by
  have parsed := secret_parse upstream primitives guards scalar secret accepted
  simp only [diversifiedPublic,parsed] at constructed
  cases identity : upstream.isIdentity (primitives.multiply generator scalar) with
  | true => simp only [publicFromPoint,identity,ite_true] at constructed; cases constructed
  | false =>
      have same : (⟨primitives.multiply generator scalar⟩ : Public S) = key :=
        Option.some.inj (by simpa only [publicFromPoint,identity,Bool.false_eq_true,ite_false] using constructed)
      exact (congrArg Public.point same).symm

theorem payment_address_relation
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream) (guards : ShielddViewingKeyAdmission.Primitives fq fr)
    (scalar : R) (secret : Secret) (key : ShortBytes) (index : Index) (address : Address S)
    (accepted : fromScalar guards scalar = some secret)
    (constructed : paymentAddress upstream primitives secret key index = some address) :
    address.diversified = diversifiedGenerator upstream primitives (diversifierForIndex upstream primitives key index) ∧
      address.transmission.point = primitives.multiply address.diversified scalar := by
  let diversifier := diversifierForIndex upstream primitives key index
  let generator := diversifiedGenerator upstream primitives diversifier
  change (match diversifiedPublic upstream primitives secret generator with
    | some publicKey => fromComponents upstream primitives diversifier publicKey
    | none => none) = some address at constructed
  cases publicRead : diversifiedPublic upstream primitives secret generator with
  | none => simp only [publicRead] at constructed; cases constructed
  | some publicKey =>
      simp only [publicRead] at constructed
      have product := diversified_public_relation upstream primitives guards scalar secret generator publicKey accepted publicRead
      change (if upstream.isIdentity generator then none else some ⟨diversifier,generator,publicKey⟩) = some address at constructed
      cases identity : upstream.isIdentity generator with
      | true => simp only [identity,ite_true] at constructed; cases constructed
      | false =>
          have same : (⟨diversifier,generator,publicKey⟩ : Address S) = address :=
            Option.some.inj (by simpa only [identity,Bool.false_eq_true,ite_false] using constructed)
          rw [← same]
          exact ⟨rfl,product⟩

theorem viewed_transmission [DecidableEq S]
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream) (guards : ShielddViewingKeyAdmission.Primitives fq fr)
    (scalar : R) (secret : Secret) (address : Address S)
    (accepted : fromScalar guards scalar = some secret)
    (viewed : viewsAddress upstream primitives secret address = true) :
    address.transmission.point = primitives.multiply address.diversified scalar := by
  cases publicRead : diversifiedPublic upstream primitives secret address.diversified with
  | none => simp only [viewsAddress,publicRead] at viewed; cases viewed
  | some key =>
      have same : key = address.transmission :=
        of_decide_eq_true (by simpa only [viewsAddress,publicRead] using viewed)
      exact (congrArg Public.point same).symm.trans
        (diversified_public_relation upstream primitives guards scalar secret address.diversified key accepted publicRead)

theorem viewed_coordinates [DecidableEq S]
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream) (guards : ShielddViewingKeyAdmission.Primitives fq fr)
    (scalar : R) (secret : Secret) (address : Address S)
    (accepted : fromScalar guards scalar = some secret)
    (viewed : viewsAddress upstream primitives secret address = true) :
    model.coordinates (upstream.embed (upstream.promote address.transmission.point)) =
      model.coordinates (fr.integer scalar • upstream.embed (upstream.promote address.diversified)) := by
  rw [viewed_transmission upstream primitives guards scalar secret address accepted viewed,
    primitives.promoteMultiply,upstream.multiplyEmbedding]

theorem payment_address_coordinates
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream) (guards : ShielddViewingKeyAdmission.Primitives fq fr)
    (scalar : R) (secret : Secret) (key : ShortBytes) (index : Index) (address : Address S)
    (accepted : fromScalar guards scalar = some secret)
    (constructed : paymentAddress upstream primitives secret key index = some address) :
    model.coordinates (upstream.embed (upstream.promote address.transmission.point)) =
      model.coordinates (fr.integer scalar • upstream.embed (upstream.promote address.diversified)) := by
  rw [(payment_address_relation upstream primitives guards scalar secret key index address accepted constructed).2,
    primitives.promoteMultiply,upstream.multiplyEmbedding]

set_option pp.all true in
#check @secret_parse
#print axioms secret_parse
set_option pp.all true in
#check @secret_from_ivk
#print axioms secret_from_ivk
set_option pp.all true in
#check @diversified_public_relation
#print axioms diversified_public_relation
set_option pp.all true in
#check @payment_address_relation
#print axioms payment_address_relation
set_option pp.all true in
#check @viewed_transmission
#print axioms viewed_transmission
set_option pp.all true in
#check @viewed_coordinates
#print axioms viewed_coordinates
set_option pp.all true in
#check @payment_address_coordinates
#print axioms payment_address_coordinates

end ShielddSecurity.ShielddNativeAddress
