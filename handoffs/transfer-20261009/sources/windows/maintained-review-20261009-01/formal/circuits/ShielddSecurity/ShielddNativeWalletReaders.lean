import ShielddSecurity.ShielddNativeWalletAssociation
import ShielddSecurity.ShielddViewingKeyCoordinates

set_option maxHeartbeats 250000

namespace ShielddSecurity.ShielddNativeWalletReaders

open GroupByteCodec

variable {F : Type} [Field F]
  {E S R K Q Signing J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
  (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
  (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
  (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
  (codec : TransferReduction.CanonicalField F)
  (parameters : Poseidon.Parameters F 6)
  (guards : ShielddViewingKeyAdmission.Primitives fq fr)
  (primitives : ShielddNativeWalletAssociation.Primitives)

/- One global canonical identity-byte law for the upstream subgroup encoder.
Together with the owned wallet parser's identity-byte guard, it proves the
separate pari key reader succeeds. It supplies no particular key's legality.
Rust refinement must bind this law to the same canonical identity encoding.
The stronger global injective encoding contract is already in Upstream. -/
variable (identityEncoding : ∀ point : S, upstream.isIdentity point = true →
  upstream.encode (upstream.promote point) = primitives.identityBytes)

variable (key : K) (walletNk : Q)
  (wallet : ShielddNativeWalletAssociation.Wallet (S := S) (R := R) (K := K) (Q := Q))
  (constructed : ShielddNativeWalletAssociation.fromComponents upstream arithmetic initial square
    codec parameters guards primitives key walletNk = some wallet)

include arithmetic initial square codec parameters guards primitives identityEncoding constructed in
theorem wallet_nonidentity :
    ShielddNativeSdk.nonidentity upstream (upstream.keyBytes key) =
      some wallet.authorizationPoint := by
  have fields := ShielddNativeWalletAssociation.constructor_fields upstream arithmetic initial
    square codec parameters guards primitives key walletNk wallet constructed
  have decoded := fields.2.2.1
  have canonical := upstream.decodedEncoding _ _ decoded
  have different := fields.2.2.2.1
  have notIdentity : upstream.isIdentity wallet.authorizationPoint = false := by
    cases identity : upstream.isIdentity wallet.authorizationPoint with
    | false => rfl
    | true =>
        have encoded := identityEncoding wallet.authorizationPoint identity
        exact False.elim (different (canonical.symm.trans encoded))
  simp only [ShielddNativeSdk.nonidentity,decoded,if_pos canonical,notIdentity,
    Bool.false_eq_true,if_false]

/-- The first two conversions in pari::authorization: the key path executes
encoding::nonidentity then native_point; the NK path executes encoding::field.
Hash parameters, IVK computation and cofactor_preimage are separate stages. -/
def inputProgram {Encoded Native : Type}
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (verification : K) (nk : Q) : Option (Group.Point F × F) :=
  match ShielddNativeSdk.key backend upstream verification with
  | none => none
  | some point =>
      match ShielddNativeSdk.field (fq := fq) backend nk with
      | none => none
      | some scalar => some (point,scalar)

include arithmetic initial square parameters guards primitives identityEncoding constructed in
theorem authorization_inputs [CharP F Scalar.modulus] {Encoded Native : Type}
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native) :
    inputProgram upstream backend wallet.ak wallet.nk =
      some (model.coordinates (upstream.embed (upstream.keyPoint key)),
        (fq.integer walletNk : F)) := by
  have fields := ShielddNativeWalletAssociation.constructor_fields upstream arithmetic initial
    square codec parameters guards primitives key walletNk wallet constructed
  have accepted := wallet_nonidentity upstream arithmetic initial square codec parameters guards
    primitives identityEncoding key walletNk wallet constructed
  rw [fields.1,fields.2.1]
  simp only [inputProgram,ShielddNativeSdk.key_read codec backend upstream key
    wallet.authorizationPoint accepted,ShielddNativeSdk.field_read]

include arithmetic initial square parameters guards primitives identityEncoding constructed in
theorem seeded_inputs [CharP F Scalar.modulus] {Encoded Native : Type}
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native) (base : Nat → F) :
    inputProgram upstream backend wallet.ak wallet.nk =
      some ((⟨ShielddViewingKeyCoordinates.seed fq fr d model upstream backend
        wallet.nk wallet.authorizationPoint base 1980,
        ShielddViewingKeyCoordinates.seed fq fr d model upstream backend
          wallet.nk wallet.authorizationPoint base 1981⟩ : Group.Point F),
        ShielddViewingKeyCoordinates.seed fq fr d model upstream backend
          wallet.nk wallet.authorizationPoint base 1993) := by
  have fields := ShielddNativeWalletAssociation.constructor_fields upstream arithmetic initial
    square codec parameters guards primitives key walletNk wallet constructed
  have point := ShielddViewingKeyCoordinates.seeded_key_coordinates fq fr d model upstream
    backend wallet.nk key wallet.authorizationPoint base fields.2.2.1
  have nk : ShielddViewingKeyCoordinates.seed fq fr d model upstream backend
      wallet.nk wallet.authorizationPoint base 1993 = (fq.integer walletNk : F) := by
    simp [ShielddViewingKeyCoordinates.seed,ShielddViewingKeySeed.seed,
      ShielddViewingKeySeed.columns,ShielddViewingKeySeed.values,patchAssignment,
      ShielddViewingKeySeed.read_value,ShielddNativeIvkHash.fqValue,fields.2.1]
  rw [point,nk]
  exact authorization_inputs upstream arithmetic initial square codec parameters guards primitives
    identityEncoding key walletNk wallet constructed backend

set_option pp.all true in
#check @wallet_nonidentity
#print axioms wallet_nonidentity
set_option pp.all true in
#check @authorization_inputs
#print axioms authorization_inputs
set_option pp.all true in
#check @seeded_inputs
#print axioms seeded_inputs

end ShielddSecurity.ShielddNativeWalletReaders
