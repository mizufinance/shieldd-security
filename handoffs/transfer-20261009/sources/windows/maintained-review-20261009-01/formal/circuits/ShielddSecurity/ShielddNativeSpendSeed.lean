import ShielddSecurity.ShielddNativeWalletAssociation

set_option maxHeartbeats 250000

namespace ShielddSecurity.ShielddNativeSpendSeed

open GroupByteCodec

variable {F : Type} [Field F]
  {E S R K Q Signing J Message Signature Nonce : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

/-- Named total native PRF/wide-decoder operations. They are not assumed to
produce a chosen secret, an honestly distributed key, or a valid FVK. The owned
constructor supplies the exact personalization and selector byte sequence. -/
structure SeedPrimitives where
  expand : List Byte → Bytes → List Byte → ShielddNativeAddress.WideBytes
  scalarWide : ShielddNativeAddress.WideBytes → R
  fieldWide : ShielddNativeAddress.WideBytes → Q

def expandLabel : List Byte := [83,104,105,101,108,100,100,95,69,120,112,97,110,100,83,100]

def deriveAsk (primitives : SeedPrimitives (R := R) (Q := Q)) (seed : Bytes) : R :=
  primitives.scalarWide (primitives.expand expandLabel seed [0])

def deriveNK (primitives : SeedPrimitives (R := R) (Q := Q)) (seed : Bytes) : Q :=
  primitives.fieldWide (primitives.expand expandLabel seed [1])

structure SpendKey where
  seed : Bytes
  ask : Signing
  wallet : ShielddNativeWalletAssociation.Wallet (S := S) (R := R) (K := K) (Q := Q)

variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
  (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
  (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
  (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
  (codec : TransferReduction.CanonicalField F) (parameters : Poseidon.Parameters F 6)
  (guards : ShielddViewingKeyAdmission.Primitives fq fr)
  (walletPrimitives : ShielddNativeWalletAssociation.Primitives)
  (seedPrimitives : SeedPrimitives (R := R) (Q := Q))

/-- Owned SpendKey::try_from(SpendKeyBytes) sequence. Canonical ASK parsing is
the upstream primitive; FVK rejection propagates. No internal retry is modeled.
The 33-byte protobuf suite/length decoder and seed-generation distribution are
separate policies, outside this already-sized32-byte constructor. -/
noncomputable def fromSeed (seed : Bytes) : Option (SpendKey (S := S) (R := R) (K := K) (Q := Q) (Signing := Signing)) :=
  match upstream.parseSigning (fr.bytes (deriveAsk seedPrimitives seed)) with
  | none => none
  | some ask =>
      (ShielddNativeWalletAssociation.fromComponents upstream arithmetic initial square codec parameters
        guards walletPrimitives (upstream.verification ask) (deriveNK seedPrimitives seed)).map
          (fun wallet => ⟨seed,ask,wallet⟩)

theorem seed_signing_parser (seed : Bytes) :
    upstream.parseSigning (fr.bytes (deriveAsk seedPrimitives seed)) =
      some (upstream.signing (deriveAsk seedPrimitives seed)) :=
  upstream.signingCanonical _

theorem seed_fields (seed : Bytes)
    (key : SpendKey (S := S) (R := R) (K := K) (Q := Q) (Signing := Signing))
    (constructed : fromSeed upstream arithmetic initial square codec parameters guards walletPrimitives seedPrimitives seed = some key) :
    key.seed = seed ∧ key.ask = upstream.signing (deriveAsk seedPrimitives seed) ∧
      ShielddNativeWalletAssociation.fromComponents upstream arithmetic initial square codec parameters
        guards walletPrimitives (upstream.verification key.ask) (deriveNK seedPrimitives seed) = some key.wallet := by
  cases made : ShielddNativeWalletAssociation.fromComponents upstream arithmetic initial square codec parameters
      guards walletPrimitives (upstream.verification (upstream.signing (deriveAsk seedPrimitives seed)))
        (deriveNK seedPrimitives seed) with
  | none => simp only [fromSeed,seed_signing_parser,made,Option.map_none] at constructed; cases constructed
  | some wallet =>
      have same : (⟨seed,upstream.signing (deriveAsk seedPrimitives seed),wallet⟩ :
          SpendKey (S := S) (R := R) (K := K) (Q := Q) (Signing := Signing)) = key :=
        Option.some.inj (by simpa only [fromSeed,seed_signing_parser,made,Option.map_some] using constructed)
      rw [← same]
      exact ⟨rfl,rfl,made⟩

theorem seed_wallet_fields (seed : Bytes)
    (key : SpendKey (S := S) (R := R) (K := K) (Q := Q) (Signing := Signing))
    (constructed : fromSeed upstream arithmetic initial square codec parameters guards walletPrimitives seedPrimitives seed = some key) :
    key.wallet.ak = upstream.verification key.ask ∧ key.wallet.nk = deriveNK seedPrimitives seed := by
  have made := (seed_fields upstream arithmetic initial square codec parameters guards walletPrimitives seedPrimitives seed key constructed).2.2
  have fields := ShielddNativeWalletAssociation.constructor_fields upstream arithmetic initial square codec parameters
    guards walletPrimitives _ _ key.wallet made
  exact ⟨fields.1,fields.2.1⟩

theorem seed_authorization_point (seed : Bytes)
    (key : SpendKey (S := S) (R := R) (K := K) (Q := Q) (Signing := Signing))
    (constructed : fromSeed upstream arithmetic initial square codec parameters guards walletPrimitives seedPrimitives seed = some key) :
    upstream.embed (upstream.keyPoint key.wallet.ak) =
      fr.integer (deriveAsk seedPrimitives seed) • upstream.embed upstream.spendAuth := by
  rw [(seed_wallet_fields upstream arithmetic initial square codec parameters guards walletPrimitives seedPrimitives seed key constructed).1,
    (seed_fields upstream arithmetic initial square codec parameters guards walletPrimitives seedPrimitives seed key constructed).2.1]
  exact upstream.verificationEmbedding _

/-- Universal native randomized-signing-key functionality. This is the exact
standard upstream operation on every signing key/randomizer, separate from
signature security, key generation and corruption/query permissions. -/
structure SigningPrimitive where
  randomize : Signing → R → Signing
  verificationRandomized : ∀ ask randomizer,
    upstream.verification (randomize ask randomizer) = upstream.randomize (upstream.verification ask) randomizer
  sign : Nonce → Signing → Message → Signature

theorem randomized_signing_argument
    (signer : SigningPrimitive (Message := Message) (Signature := Signature) (Nonce := Nonce) upstream)
    (seed : Bytes) (key : SpendKey (S := S) (R := R) (K := K) (Q := Q) (Signing := Signing))
    (constructed : fromSeed upstream arithmetic initial square codec parameters guards walletPrimitives seedPrimitives seed = some key)
    (randomizer : R) :
    upstream.verification (signer.randomize key.ask randomizer) =
      ShielddNativeSdk.planRk upstream key.wallet.ak randomizer := by
  rw [signer.verificationRandomized,
    (seed_wallet_fields upstream arithmetic initial square codec parameters guards walletPrimitives seedPrimitives seed key constructed).1]
  rfl

def signatureRequest
    (signer : SigningPrimitive (Message := Message) (Signature := Signature) (Nonce := Nonce) upstream)
    (key : SpendKey (S := S) (R := R) (K := K) (Q := Q) (Signing := Signing))
    (randomizer : R) (message : Message) (nonce : Nonce) : K × Message × Signature :=
  (upstream.verification (signer.randomize key.ask randomizer),message,
    signer.sign nonce (signer.randomize key.ask randomizer) message)

theorem signature_request_arguments
    (signer : SigningPrimitive (Message := Message) (Signature := Signature) (Nonce := Nonce) upstream)
    (seed : Bytes) (key : SpendKey (S := S) (R := R) (K := K) (Q := Q) (Signing := Signing))
    (constructed : fromSeed upstream arithmetic initial square codec parameters guards walletPrimitives seedPrimitives seed = some key)
    (randomizer : R) (message : Message) (nonce : Nonce) :
    (signatureRequest upstream signer key randomizer message nonce).1 = ShielddNativeSdk.planRk upstream key.wallet.ak randomizer ∧
      (signatureRequest upstream signer key randomizer message nonce).2.1 = message ∧
      (signatureRequest upstream signer key randomizer message nonce).2.2 =
        signer.sign nonce (signer.randomize key.ask randomizer) message :=
  ⟨randomized_signing_argument upstream arithmetic initial square codec parameters guards walletPrimitives seedPrimitives signer seed key constructed randomizer,rfl,rfl⟩

set_option pp.all true in
#check @seed_signing_parser
#print axioms seed_signing_parser
set_option pp.all true in
#check @seed_fields
#print axioms seed_fields
set_option pp.all true in
#check @seed_wallet_fields
#print axioms seed_wallet_fields
set_option pp.all true in
#check @seed_authorization_point
#print axioms seed_authorization_point
set_option pp.all true in
#check @randomized_signing_argument
#print axioms randomized_signing_argument
set_option pp.all true in
#check @signature_request_arguments
#print axioms signature_request_arguments

end ShielddSecurity.ShielddNativeSpendSeed
