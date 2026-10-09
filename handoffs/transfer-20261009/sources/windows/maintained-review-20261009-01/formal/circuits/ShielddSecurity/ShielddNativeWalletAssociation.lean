import ShielddSecurity.ShielddNativeIvkSdkProgram
import ShielddSecurity.ShielddNativeAddress

set_option maxHeartbeats 300000

namespace ShielddSecurity.ShielddNativeWalletAssociation

open GroupByteCodec

variable {F : Type} [Field F]
  {E S R K Q Signing J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

/-- Global PRF callback and canonical identity encoding. No distribution,
key ownership, address success or selected witness equality is supplied. The
PRF is an unrestricted total function; the owned labels and slices are below.
The identity encoding is the upstream canonical SubgroupPoint identity bytes.
Rust callback/parameter correspondence remains an explicit source obligation. -/
structure Primitives where
  identityBytes : Bytes
  expand : List Byte → Bytes → Bytes → ShielddNativeAddress.WideBytes

structure Wallet where
  ak : K
  nk : Q
  authorizationPoint : S
  scalar : R
  outgoing : Bytes
  diversificationKey : ShielddNativeAddress.ShortBytes

def ovkLabel : List Byte := [83,104,105,101,108,100,100,68,101,114,105,118,101,79,86,75]
def dkLabel : List Byte := [83,104,105,101,108,100,100,95,68,101,114,105,118,101,68,75]

def first32 (bytes : ShielddNativeAddress.WideBytes) : Bytes :=
  fun index => bytes ⟨index.val,by omega⟩

def first16 (bytes : ShielddNativeAddress.WideBytes) : ShielddNativeAddress.ShortBytes :=
  fun index => bytes ⟨index.val,by omega⟩

variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
  (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
  (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
  (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
  (codec : TransferReduction.CanonicalField F)
  (parameters : Poseidon.Parameters F 6)
  (guards : ShielddViewingKeyAdmission.Primitives fq fr)
  (primitives : Primitives)

def incomingHash (nk : Q) (point : S) : Q :=
  ShielddNativeIvkSdkProgram.ivk fq arithmetic initial square codec parameters nk
    (ShielddNativeSdk.coordinateX upstream point) (ShielddNativeSdk.coordinateY upstream point)

theorem incoming_hash_source (nk : Q) (point : S) :
    ShielddNativeIvkHash.fqValue (F := F) fq
      (incomingHash upstream arithmetic initial square codec parameters nk point) =
      Poseidon.hash6 parameters 16 [ShielddNativeIvkHash.fqValue (F := F) fq nk,
        ShielddNativeIvkHash.fqValue (F := F) fq (ShielddNativeSdk.coordinateX upstream point),
        ShielddNativeIvkHash.fqValue (F := F) fq (ShielddNativeSdk.coordinateY upstream point)] :=
  ShielddNativeIvkSdkProgram.ivk_value fq arithmetic initial square codec parameters nk
    (ShielddNativeSdk.coordinateX upstream point) (ShielddNativeSdk.coordinateY upstream point)

/-- Owned encoding::point re-encoding check. The globally canonical native
decoder law discharges the check, rather than assuming the whole wrapper. -/
noncomputable def canonicalPoint (bytes : Bytes) : Option S := by
  classical
  exact match upstream.decodePoint bytes with
    | none => none
    | some point => if upstream.encode (upstream.promote point) = bytes then some point else none

theorem canonical_point_decoder (bytes : Bytes) :
    canonicalPoint upstream bytes = upstream.decodePoint bytes := by
  classical
  cases decoded : upstream.decodePoint bytes with
  | none => simp only [canonicalPoint,decoded]
  | some point => simp only [canonicalPoint,decoded,if_pos (upstream.decodedEncoding _ _ decoded)]

/-- Owned FVK source projection: decode actual AK bytes, hash wallet NK and
decoded AK coordinates, reject the identity encoding, then apply the exact
wide-reduction/nonzero guard. Retain the original AK/NK and exact PRF slices.
Other FVK accessors and serialization are outside this constructor projection.
In particular, this successful constructor does not assert views_address for
an arbitrary sender supplied to transfer_public_private. -/
noncomputable def fromComponents (ak : K) (nk : Q) : Option (Wallet (S := S) (R := R) (K := K) (Q := Q)) := by
  classical
  exact match canonicalPoint upstream (upstream.keyBytes ak) with
    | none => none
    | some point =>
      let hash := incomingHash upstream arithmetic initial square codec parameters nk point
      if upstream.keyBytes ak = primitives.identityBytes then none else
      match ShielddViewingKeyAdmission.incomingScalar guards hash with
      | none => none
      | some scalar => some {
          ak := ak, nk := nk, authorizationPoint := point, scalar := scalar
          outgoing := first32 (primitives.expand ovkLabel (fq.bytes nk) (upstream.keyBytes ak))
          diversificationKey := first16 (primitives.expand dkLabel (fq.bytes nk) (upstream.keyBytes ak)) }

theorem constructor_fields (ak : K) (nk : Q) (wallet : Wallet (S := S) (R := R) (K := K) (Q := Q))
    (constructed : fromComponents upstream arithmetic initial square codec parameters guards primitives ak nk = some wallet) :
    wallet.ak = ak ∧ wallet.nk = nk ∧
      upstream.decodePoint (upstream.keyBytes ak) = some wallet.authorizationPoint ∧
      upstream.keyBytes ak ≠ primitives.identityBytes ∧
      ShielddViewingKeyAdmission.incomingScalar guards
        (incomingHash upstream arithmetic initial square codec parameters nk wallet.authorizationPoint) = some wallet.scalar ∧
      wallet.outgoing = first32 (primitives.expand ovkLabel (fq.bytes nk) (upstream.keyBytes ak)) ∧
      wallet.diversificationKey = first16 (primitives.expand dkLabel (fq.bytes nk) (upstream.keyBytes ak)) := by
  classical
  cases decoded : upstream.decodePoint (upstream.keyBytes ak) with
  | none => simp only [fromComponents,canonical_point_decoder,decoded] at constructed; cases constructed
  | some point =>
      by_cases identity : upstream.keyBytes ak = primitives.identityBytes
      · simp only [fromComponents,canonical_point_decoder,decoded,if_pos identity] at constructed
        cases constructed
      · cases reduced : ShielddViewingKeyAdmission.incomingScalar guards
          (incomingHash upstream arithmetic initial square codec parameters nk point) with
        | none => simp only [fromComponents,canonical_point_decoder,decoded,if_neg identity,reduced] at constructed; cases constructed
        | some scalar =>
            have same :
                ({ ak := ak
                   nk := nk
                   authorizationPoint := point
                   scalar := scalar
                   outgoing := first32 (primitives.expand ovkLabel (fq.bytes nk) (upstream.keyBytes ak))
                   diversificationKey := first16 (primitives.expand dkLabel (fq.bytes nk) (upstream.keyBytes ak)) } :
                Wallet (S := S) (R := R) (K := K) (Q := Q)) = wallet :=
              Option.some.inj (by simpa only [fromComponents,canonical_point_decoder,decoded,if_neg identity,reduced] using constructed)
            rw [← same]
            exact ⟨rfl,rfl,(by simpa only [decoded] using decoded),identity,
              (by simpa only [reduced] using reduced),rfl,rfl⟩

theorem decoded_key_association (key : K) (point : S)
    (decoded : upstream.decodePoint (upstream.keyBytes key) = some point) :
    upstream.embed (upstream.promote point) = upstream.embed (upstream.keyPoint key) := by
  apply upstream.encodingInjective
  exact (upstream.decodedEncoding _ _ decoded).trans (upstream.keyBytesBody key)

theorem constructor_scalar (ak : K) (nk : Q) (wallet : Wallet (S := S) (R := R) (K := K) (Q := Q))
    (constructed : fromComponents upstream arithmetic initial square codec parameters guards primitives ak nk = some wallet) :
    fr.integer wallet.scalar =
      fq.integer (incomingHash upstream arithmetic initial square codec parameters nk wallet.authorizationPoint) % Scalar.order ∧
      0 < fr.integer wallet.scalar ∧ fr.integer wallet.scalar < Scalar.order := by
  have accepted := (constructor_fields upstream arithmetic initial square codec parameters guards primitives ak nk wallet constructed).2.2.2.2.1
  have scalar := ShielddViewingKeyAdmission.successful_scalar guards _ wallet.scalar accepted
  refine ⟨?_,scalar.2⟩
  rw [scalar.1,ShielddViewingKeyAdmission.reduce_integer]

theorem constructor_secret (ak : K) (nk : Q) (wallet : Wallet (S := S) (R := R) (K := K) (Q := Q))
    (constructed : fromComponents upstream arithmetic initial square codec parameters guards primitives ak nk = some wallet) :
    ShielddNativeAddress.fromScalar guards wallet.scalar = some ⟨fr.bytes wallet.scalar⟩ :=
  ShielddNativeAddress.secret_from_ivk guards _ wallet.scalar
    (constructor_fields upstream arithmetic initial square codec parameters guards primitives ak nk wallet constructed).2.2.2.2.1

theorem payment_address_association
    (addressPrimitives : ShielddNativeAddress.Primitives upstream)
    (ak : K) (nk : Q) (wallet : Wallet (S := S) (R := R) (K := K) (Q := Q))
    (constructed : fromComponents upstream arithmetic initial square codec parameters guards primitives ak nk = some wallet)
    (index : ShielddNativeAddress.Index) (address : ShielddNativeAddress.Address S)
    (payment : ShielddNativeAddress.paymentAddress upstream addressPrimitives
      ⟨fr.bytes wallet.scalar⟩ wallet.diversificationKey index = some address) :
    address.transmission.point = addressPrimitives.multiply address.diversified wallet.scalar :=
  (ShielddNativeAddress.payment_address_relation upstream addressPrimitives guards wallet.scalar _
    wallet.diversificationKey index address
    (constructor_secret upstream arithmetic initial square codec parameters guards primitives ak nk wallet constructed) payment).2

theorem viewed_address_association [DecidableEq S]
    (addressPrimitives : ShielddNativeAddress.Primitives upstream)
    (ak : K) (nk : Q) (wallet : Wallet (S := S) (R := R) (K := K) (Q := Q))
    (constructed : fromComponents upstream arithmetic initial square codec parameters guards primitives ak nk = some wallet)
    (address : ShielddNativeAddress.Address S)
    (viewed : ShielddNativeAddress.viewsAddress upstream addressPrimitives ⟨fr.bytes wallet.scalar⟩ address = true) :
    address.transmission.point = addressPrimitives.multiply address.diversified wallet.scalar :=
  ShielddNativeAddress.viewed_transmission upstream addressPrimitives guards wallet.scalar _ address
    (constructor_secret upstream arithmetic initial square codec parameters guards primitives ak nk wallet constructed) viewed

structure Authorization where
  ak : K
  nk : Q
  rk : K
  randomizer : R
  sender : ShielddNativeAddress.Address S

def proofArguments (wallet : Wallet (S := S) (R := R) (K := K) (Q := Q))
    (randomizer : R) (sender : ShielddNativeAddress.Address S) : Authorization (S := S) (R := R) (K := K) (Q := Q) :=
  ⟨wallet.ak,wallet.nk,upstream.randomize wallet.ak randomizer,randomizer,sender⟩

theorem proof_arguments_association (wallet : Wallet (S := S) (R := R) (K := K) (Q := Q))
    (randomizer : R) (sender : ShielddNativeAddress.Address S) :
    (proofArguments upstream wallet randomizer sender).ak = wallet.ak ∧
      (proofArguments upstream wallet randomizer sender).nk = wallet.nk ∧
      (proofArguments upstream wallet randomizer sender).randomizer = randomizer ∧
      (proofArguments upstream wallet randomizer sender).sender = sender ∧
      upstream.embed (upstream.keyPoint (proofArguments upstream wallet randomizer sender).rk) =
        upstream.embed (upstream.keyPoint wallet.ak) + fr.integer randomizer • upstream.embed upstream.spendAuth := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  change upstream.embed (upstream.keyPoint (upstream.randomize wallet.ak randomizer)) = _
  rw [upstream.randomizeBody,upstream.addEmbedding,upstream.multiplyEmbedding]

/-- Exact unregulated ActionWitness::nullifier_key early return. The function
has no address guard: success conveys only this stored wallet NK association.
Regulated effective NK construction and its explicit views_address check are
separate from the wallet NK used by the IVK hash and TransferProofPrivate. -/
def unregulatedNullifierKey (wallet : Wallet (S := S) (R := R) (K := K) (Q := Q))
    (_sender : ShielddNativeAddress.Address S) : Option Q := some wallet.nk

theorem unregulated_nk_only (wallet : Wallet (S := S) (R := R) (K := K) (Q := Q))
    (sender : ShielddNativeAddress.Address S) : unregulatedNullifierKey wallet sender = some wallet.nk := rfl

set_option pp.all true in
#check @incoming_hash_source
#print axioms incoming_hash_source
set_option pp.all true in
#check @canonical_point_decoder
#print axioms canonical_point_decoder
set_option pp.all true in
#check @constructor_fields
#print axioms constructor_fields
set_option pp.all true in
#check @decoded_key_association
#print axioms decoded_key_association
set_option pp.all true in
#check @constructor_scalar
#print axioms constructor_scalar
set_option pp.all true in
#check @constructor_secret
#print axioms constructor_secret
set_option pp.all true in
#check @payment_address_association
#print axioms payment_address_association
set_option pp.all true in
#check @viewed_address_association
#print axioms viewed_address_association
set_option pp.all true in
#check @proof_arguments_association
#print axioms proof_arguments_association
set_option pp.all true in
#check @unregulated_nk_only
#print axioms unregulated_nk_only

end ShielddSecurity.ShielddNativeWalletAssociation
