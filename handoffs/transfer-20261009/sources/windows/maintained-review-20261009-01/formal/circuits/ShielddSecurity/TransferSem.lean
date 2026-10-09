import ShielddSecurity.TransferCore

set_option maxHeartbeats 200000

/-! Independent semantic target for the current Transfer constructor graph.
Cryptographic operations are explicit interpretation parameters, not records of
claimed circuit conclusions. No row evaluator, runtime witness callback, source
handle or verification capability occurs here. Exact deployed operation/domain
interpretations and all circuit/source refinements remain separate obligations. -/
namespace ShielddSecurity.TransferSem

open TransferCore

inductive Domain
  | state
  | asset
  | compliance
  | volumeSubject
  | volumeState
  | volumeOriginNullifier
  | noteNullifier
  | volumePaddingCommitment
  | volumePaddingNullifier
  | encryptionStream
  | sharedSecret
  | detection
  | keyConfirmation
  | salt
  | note
  | incomingViewingKey
  | regulatedNullifierKey
  | regulatedNullifierCommitment
  | complianceLeaf
  | recoveryCommitment
  | recoveryConfirmation
  | dummyNullifier
  | registryParameters
  | registryRing
  | registryLeaf
  | assetGenerator
  | unregulatedDetection
  | unregulatedRing
  | route
  | routeRandomness
  | routePermutation
  | routeParameters
  | transferStatement
  | ownership
  | auditKeys
  | policyIdentifier
  deriving DecidableEq

/-- Closed exact domain codes from primitives/src/domains.rs at the source pin.
Arity remains the length of each explicit input list. Interpretation must use
the deployed arity-dependent Poseidon IV, not just the domain code. -/
def domainCode : Domain → Nat
  | .state => 1
  | .asset => 2
  | .compliance => 3
  | .volumeSubject => 4
  | .volumeState => 5
  | .volumeOriginNullifier => 6
  | .noteNullifier => 7
  | .volumePaddingCommitment => 8
  | .volumePaddingNullifier => 9
  | .encryptionStream => 10
  | .sharedSecret => 11
  | .detection => 12
  | .keyConfirmation => 13
  | .salt => 14
  | .note => 15
  | .incomingViewingKey => 16
  | .regulatedNullifierKey => 17
  | .regulatedNullifierCommitment => 18
  | .complianceLeaf => 19
  | .recoveryCommitment => 20
  | .recoveryConfirmation => 21
  | .dummyNullifier => 22
  | .registryParameters => 23
  | .registryRing => 24
  | .registryLeaf => 25
  | .assetGenerator => 26
  | .unregulatedDetection => 28
  | .unregulatedRing => 29
  | .route => 30
  | .routeRandomness => 31
  | .routePermutation => 32
  | .routeParameters => 33
  | .transferStatement => 34
  | .ownership => 35
  | .auditKeys => 36
  | .policyIdentifier => 37

structure Crypto where
  hash : Domain → List Nat → Nat
  subgroup : Affine → Prop
  add : Affine → Affine → Affine
  mul : Nat → Affine → Affine
  assetGenerator : Nat → Affine
  fingerprint : Address → Affine
  addressWords : Address → Fin 3 → Nat
  generator : Affine
  blindingGenerator : Affine
  unregulatedDetection : Affine
  unregulatedRing : Affine
  emptyPolicy : Nat

abbrev Path (depth : Nat) := Fin depth → Fin 3 → Nat

def pointFields (p : Affine) : List Nat := [p.x, p.y]
def addressFields (a : Address) : List Nat :=
  pointFields a.diversified ++ pointFields a.transmission

def nonidentity (p : Affine) : Prop := p ≠ ⟨0, 1⟩
def ValidPoint (c : Crypto) (p : Affine) : Prop := CanonicalAffine p ∧ c.subgroup p

def treeRoot (c : Crypto) (tree : Domain) (depth position leaf : Nat)
    (siblings : Nat → Fin 3 → Nat) : Nat :=
  (List.range depth).foldl (fun node level =>
    let slot := position / 4 ^ level % 4
    let children := if slot = 0 then [node, siblings level 0, siblings level 1, siblings level 2]
      else if slot = 1 then [siblings level 0, node, siblings level 1, siblings level 2]
      else if slot = 2 then [siblings level 0, siblings level 1, node, siblings level 2]
      else [siblings level 0, siblings level 1, siblings level 2, node]
    c.hash tree ([level + 1] ++ children)) leaf

/-- Out-of-range siblings are irrelevant: every actual lookup is below depth. -/
def root (c : Crypto) (tree : Domain) {depth : Nat} (position leaf : Nat)
    (siblings : Path depth) : Nat :=
  treeRoot c tree depth position leaf (fun level slot =>
    if h : level < depth then siblings ⟨level, h⟩ slot else 0)

structure User where
  address : Address
  rnkDH : Affine
  rnkCommitment : Nat
  lifecycle : Nat
  position : Nat
  siblings : Path 16

structure AuditKeys where
  epoch : Nat
  payload : Affine
  checking : Affine

structure AssetLeaf where
  value : Nat
  nextIndex : Nat
  nextValue : Nat
  detection : Affine
  dailyLimit : Nat
  routePolicy : Nat
  ring : Affine
  ringID : Nat
  policyID : Nat
  permission : Nat
  resource : Nat
  audit : AuditKeys
  position : Nat
  siblings : Path 16

structure Authorization where
  ak : Affine
  nk : Nat
  ivk : Nat
  quotient : Nat
  randomizer : Nat
  rk : Affine

structure Spend where
  blinding : Nat
  amount : Nat
  recovery : Nat
  position : Nat
  siblings : Path 24
  nullifier : Nat

structure Recovery where
  epk : Affine
  c2 : Nat
  salt : Nat
  confirmation : Nat
  encryptedAmount : Nat
  encryptedBlinding : Nat
  commitment : Nat
  seed : Nat
  randomizer : Nat

structure Output where
  blinding : Nat
  amount : Nat
  recovery : Recovery
  noteCommitment : Nat

structure Volume where
  nullifier : Nat
  commitment : Nat
  dayStart : Nat
  context : Nat
  useReal : Bool
  startsNewDay : Bool
  dayIndex : Nat
  second : Nat
  subject : Nat
  prior : Nat
  priorBlinding : Nat
  priorCommitment : Nat
  priorPosition : Nat
  priorSiblings : Path 24
  successor : Nat
  successorBlinding : Nat

structure Routing where
  regulatedPrecision : Nat
  unregulatedPrecision : Nat
  height : Nat
  parameterSet : Nat
  tags : Fin 2 → Nat

structure Tier where
  ephemeral : Nat
  epk : Affine
  c2 : Nat
  ciphertext : Fin 3 → Nat
  confirmation : Nat

structure Ownership where
  randomness : Nat
  r : Affine
  c : Affine

structure Encryption where
  detection : Fin 4 → Nat
  tiers : Fin 4 → Tier
  policy : Fin 4 → Nat
  timestamp : Nat
  salts : Fin 4 → Nat
  auditEpoch : Nat
  ownership : Fin 2 → Ownership

structure Witness where
  anchor : Nat
  assetAnchor : Nat
  userAnchor : Nat
  asset : Nat
  regulated : Bool
  timestamp : Nat
  nonce : Nat
  blinding : Nat
  registry : AssetLeaf
  sender : User
  receiver : User
  auth : Authorization
  spends : Fin 2 → Spend
  optionalDummy : Bool
  paddingSeed : Nat
  outputs : Fin 2 → Output
  volume : Volume
  routing : Routing
  encryption : Encryption

-- The semantic field operations use canonical natural representatives.
def fadd (a b : Nat) : Nat := (a + b) % fieldModulus
def fsub (a b : Nat) : Nat := (a % fieldModulus + fieldModulus - b % fieldModulus) % fieldModulus

def userLeaf (c : Crypto) (asset : Nat) (u : User) : Nat :=
  c.hash .complianceLeaf (addressFields u.address ++ [asset] ++
    pointFields u.rnkDH ++ [u.rnkCommitment, u.lifecycle])

def UserSem (c : Crypto) (w : Witness) (u : User) : Prop :=
  ValidPoint c u.address.diversified ∧ nonidentity u.address.diversified ∧
  ValidPoint c u.address.transmission ∧ nonidentity u.address.transmission ∧
  ValidPoint c u.rnkDH ∧ nonidentity u.rnkDH ∧
  u.lifecycle < 2 ^ 131 ∧ u.position < 2 ^ 32 ∧
  (w.regulated = true →
    u.lifecycle % 8 = 1 ∧ u.lifecycle / 2 ^ 67 = 0 ∧
    root c .compliance u.position (userLeaf c w.asset u) u.siblings = w.userAnchor)

def assetLeaf (c : Crypto) (l : AssetLeaf) : Nat :=
  let parameters := c.hash .registryParameters (pointFields l.detection ++ [l.dailyLimit, l.routePolicy])
  let ring := c.hash .registryRing (pointFields l.ring ++ [l.ringID, l.policyID, l.permission, l.resource])
  let audit := c.hash .auditKeys ([l.audit.epoch] ++ pointFields l.audit.payload ++ pointFields l.audit.checking)
  c.hash .registryLeaf [l.value, l.nextIndex, l.nextValue, parameters,
    c.hash .registryRing [ring, audit]]

def RegistrySem (c : Crypto) (w : Witness) : Prop :=
  let l := w.registry
  ValidPoint c l.detection ∧ ValidPoint c l.ring ∧
  ValidPoint c l.audit.payload ∧ ValidPoint c l.audit.checking ∧
  l.audit.epoch < 2 ^ 64 ∧ l.position < 2 ^ 32 ∧
  l.value < fieldModulus ∧ w.asset < fieldModulus ∧ l.nextValue < fieldModulus ∧
  root c .asset l.position (assetLeaf c l) l.siblings = w.assetAnchor ∧
  (if w.regulated then
    w.asset = l.value ∧ l.audit.epoch ≠ 0 ∧
    nonidentity l.audit.payload ∧ nonidentity l.audit.checking ∧
    l.audit.payload ≠ c.unregulatedRing ∧ l.audit.checking ≠ c.unregulatedRing ∧
    l.audit.payload ≠ l.audit.checking
   else l.value < w.asset ∧ w.asset < l.nextValue)

def ring (c : Crypto) (w : Witness) : Affine :=
  if w.regulated then w.registry.ring else c.unregulatedRing

def rnk (c : Crypto) (w : Witness) : Nat :=
  c.hash .regulatedNullifierKey (pointFields (c.mul w.auth.ivk w.sender.rnkDH) ++
    addressFields w.sender.address ++ [w.asset] ++ pointFields (ring c w))

def effectiveNK (c : Crypto) (w : Witness) : Nat :=
  if w.regulated then rnk c w else w.auth.nk

def AuthorizationScalarSem (c : Crypto) (w : Witness) : Prop :=
  w.auth.ivk < scalarOrder ∧ w.auth.ivk ≠ 0 ∧ w.auth.quotient ≤ 8 ∧
  c.hash .incomingViewingKey ([w.auth.nk] ++ pointFields w.auth.ak) =
    w.auth.ivk + scalarOrder * w.auth.quotient

def AuthorizationSem (c : Crypto) (w : Witness) : Prop :=
  ValidPoint c w.auth.ak ∧ nonidentity w.auth.ak ∧ w.asset ≠ 0 ∧
  nonidentity (ring c w) ∧ AuthorizationScalarSem c w ∧
  c.mul w.auth.ivk w.sender.address.diversified = w.sender.address.transmission ∧
  nonidentity (c.mul w.auth.ivk w.sender.rnkDH) ∧
  (w.regulated = true → c.hash .regulatedNullifierCommitment [rnk c w] = w.sender.rnkCommitment) ∧
  w.auth.randomizer < scalarOrder ∧ ValidPoint c w.auth.rk ∧ nonidentity w.auth.rk ∧
  w.auth.rk = c.add w.auth.ak (c.mul w.auth.randomizer c.generator)

def noteCommitment (c : Crypto) (asset : Nat) (address : Address)
    (blinding amount recovery : Nat) : Nat :=
  c.hash .note ([blinding, amount, asset] ++ addressFields address ++ [recovery])

def SpendSem (c : Crypto) (w : Witness) (slot : Fin 2) : Prop :=
  let s := w.spends slot
  let commitment := noteCommitment c w.asset w.sender.address s.blinding s.amount s.recovery
  s.amount < amountBound ∧ s.position < 2 ^ 48 ∧
  (if slot.val = 1 ∧ w.optionalDummy = true then
    s.amount = 0 ∧ s.nullifier = c.hash .dummyNullifier [w.paddingSeed, w.auth.randomizer, 1]
   else s.nullifier = c.hash .noteNullifier [effectiveNK c w, commitment, s.position] ∧
     root c .state s.position commitment s.siblings = w.anchor)

def payloadKey (c : Crypto) (w : Witness) : Affine :=
  if w.regulated then w.registry.audit.payload else c.unregulatedRing

def secret (c : Crypto) (p : Affine) : Nat := c.hash .sharedSecret (pointFields p)
def stream (c : Crypto) (seed counter : Nat) : Nat := c.hash .encryptionStream [seed, counter]

def OutputSem (c : Crypto) (w : Witness) (slot : Fin 2) : Prop :=
  let o := w.outputs slot
  let a := if slot.val = 0 then w.receiver.address else w.sender.address
  let r := o.recovery
  o.amount < amountBound ∧ (slot.val = 0 → o.amount ≠ 0) ∧
  o.noteCommitment = noteCommitment c w.asset a o.blinding o.amount r.commitment ∧
  r.randomizer < scalarOrder ∧ r.epk = c.mul r.randomizer c.generator ∧ nonidentity r.epk ∧
  r.c2 = fadd r.seed (secret c (c.mul r.randomizer (payloadKey c w))) ∧
  r.confirmation = c.hash .recoveryConfirmation ([r.seed] ++ pointFields r.epk ++ [r.salt]) ∧
  r.encryptedAmount = fadd o.amount (stream c r.seed 0) ∧
  r.encryptedBlinding = fadd o.blinding (stream c r.seed 1) ∧
  r.commitment = c.hash .recoveryCommitment (pointFields r.epk ++
    [r.c2, r.salt, r.confirmation, r.encryptedAmount, r.encryptedBlinding])


def external (w : Witness) : Bool := decide (w.sender.address ≠ w.receiver.address)
def eligible (w : Witness) : Bool := decide (w.volume.context = 1) && w.regulated && external w
def flagged (w : Witness) : Bool := eligible w && !w.volume.useReal

def volumeState (c : Crypto) (subject day amount blinding : Nat) : Nat :=
  c.hash .volumeState [subject, day, amount, blinding]

def VolumeSem (c : Crypto) (w : Witness) : Prop :=
  let v := w.volume
  let prior := volumeState c v.subject v.dayStart v.prior v.priorBlinding
  let realNF := if v.startsNewDay then
    c.hash .volumeOriginNullifier [w.auth.nk, v.subject, v.dayStart]
    else c.hash .noteNullifier [w.auth.nk, prior, v.priorPosition]
  let paddingInputs := [w.auth.nk, w.nonce, v.dayStart]
  w.timestamp < 2 ^ 64 ∧ v.dayIndex < 2 ^ 48 ∧ v.second ≤ 86399 ∧
  w.timestamp = 86400 * v.dayIndex + v.second ∧
  (v.context = 1 ∨ v.context = 2) ∧
  (v.context = 2 → external w = false) ∧
  v.dayStart = (if v.context = 1 then 86400 * v.dayIndex else 0) ∧
  v.prior < amountBound ∧ v.successor < amountBound ∧ w.registry.dailyLimit < amountBound ∧
  v.prior + (w.outputs 0).amount < amountBound ∧ v.priorPosition < 2 ^ 48 ∧
  (v.useReal = true → eligible w = true ∧
    v.subject = c.hash .volumeSubject (addressFields w.sender.address ++ [w.asset]) ∧
    v.successor = v.prior + (w.outputs 0).amount ∧ v.successor ≤ w.registry.dailyLimit ∧
    (if v.startsNewDay then v.prior = 0 else
      v.priorCommitment = prior ∧ root c .state v.priorPosition prior v.priorSiblings = w.anchor)) ∧
  v.nullifier = (if v.context = 2 then 0 else if v.useReal then realNF
    else c.hash .volumePaddingNullifier paddingInputs) ∧
  v.commitment = (if v.context = 2 then 0 else if v.useReal then
    volumeState c v.subject v.dayStart v.successor v.successorBlinding
    else c.hash .volumePaddingCommitment paddingInputs)

def RoutingSem (c : Crypto) (w : Witness) : Prop :=
  let r := w.routing
  let precision := if w.regulated then r.regulatedPrecision else r.unregulatedPrecision
  let swapped := decide (c.hash .routePermutation [w.nonce] % 2 = 1)
  r.regulatedPrecision ≤ r.unregulatedPrecision ∧ r.unregulatedPrecision ≤ 32 ∧
  r.parameterSet = c.hash .routeParameters [r.regulatedPrecision, r.unregulatedPrecision, r.height] ∧
  ∀ slot : Fin 2,
    let senderSlot := decide (if swapped then slot.val = 1 else slot.val = 0)
    let meaningful := !senderSlot || w.regulated || (w.outputs 1).amount != 0
    let point := if senderSlot then w.sender.address.transmission else w.receiver.address.transmission
    let word := c.hash .route (pointFields point)
    let random := c.hash .routeRandomness [w.nonce, slot.val]
    r.tags slot < 2 ^ 32 ∧ ∀ bit : Fin 32,
      r.tags slot / 2 ^ bit.val % 2 =
        (if meaningful && decide (bit.val < precision) then word else random) / 2 ^ bit.val % 2

def detectionKey (c : Crypto) (w : Witness) : Affine :=
  if w.regulated then w.registry.detection else c.unregulatedDetection

def checkingKey (c : Crypto) (w : Witness) : Affine :=
  if w.regulated then w.registry.audit.checking else c.unregulatedRing

def salt (c : Crypto) (w : Witness) (slot : Nat) : Nat := c.hash .salt [w.nonce, slot]

def EncryptionSem (c : Crypto) (w : Witness) : Prop :=
  let e := w.encryption
  let selected := if flagged w then detectionKey c w else payloadKey c w
  let tier0 := e.tiers 0
  let detectionSeed := c.hash .detection
    (pointFields (c.mul tier0.ephemeral (detectionKey c w)) ++ pointFields tier0.epk)
  nonidentity (detectionKey c w) ∧
  e.timestamp = w.timestamp ∧
  e.auditEpoch = (if w.regulated then w.registry.audit.epoch else 0) ∧
  (∀ i : Fin 4, e.policy i = if w.regulated then
    ([w.registry.ringID, w.registry.policyID, w.registry.resource, w.registry.permission][i.val]!)
    else c.emptyPolicy) ∧
  (∀ i : Fin 4, e.salts i = salt c w (i.val + 1)) ∧
  (∀ i : Fin 4,
    let plaintext := [w.asset, salt c w 0, if flagged w then 1 else 0, 0][i.val]!
    e.detection i = fadd plaintext (stream c detectionSeed i.val)) ∧
  (∀ i : Fin 4,
    let tier := e.tiers i
    let seed := fsub tier.c2 (secret c (c.mul tier.ephemeral selected))
    tier.ephemeral < scalarOrder ∧ tier.epk = c.mul tier.ephemeral c.generator ∧ nonidentity tier.epk ∧
    (if i.val = 0 ∨ i.val = 2 then
      tier.confirmation = c.hash .keyConfirmation ([seed] ++ pointFields tier.epk ++ [salt c w (i.val + 1)]) ∧
      tier.ciphertext 0 = fadd (w.outputs 0).amount (stream c seed 0)
     else ∀ j : Fin 3,
       tier.ciphertext j = fadd (c.addressWords (if i.val = 1 then w.receiver.address else w.sender.address) j)
         (stream c seed j.val))) ∧
  (∀ i : Fin 2,
    let ownership := e.ownership i
    let address := if i.val = 0 then w.sender.address else w.receiver.address
    ownership.randomness < scalarOrder ∧ ownership.r = c.mul ownership.randomness c.generator ∧
    nonidentity ownership.r ∧ nonidentity (checkingKey c w) ∧
    ownership.c = c.add (c.fingerprint address) (c.mul ownership.randomness (checkingKey c w)))

/-- Algebraic commitment semantics; binding/knowledge is an additional
computational contract and is not inferred from this expression. -/
def balance (c : Crypto) (w : Witness) : Affine :=
  let inputs := (w.spends 0).amount + (w.spends 1).amount
  let outputs := (w.outputs 0).amount + (w.outputs 1).amount
  let signed := ((inputs : Int) - (outputs : Int)) % (scalarOrder : Int)
  c.add (c.mul signed.toNat (c.assetGenerator w.asset))
    (c.mul w.blinding c.blindingGenerator)

/-- Independently stated balance input domain. It does not require zero net:
actions contribute signed amounts and the transaction binding layer composes them. -/
def BalanceInputsSem (in0 in1 out0 out1 blinding : Nat) : Prop :=
  in0 < amountBound ∧ in1 < amountBound ∧ out0 < amountBound ∧ out1 < amountBound ∧
  blinding < scalarOrder

/-- The owned balance gadget rejects an identity asset generator for this
asset. Canonical coordinates alone do not establish this condition. -/
def BalanceSem (c : Crypto) (w : Witness) : Prop :=
  BalanceInputsSem (w.spends 0).amount (w.spends 1).amount
    (w.outputs 0).amount (w.outputs 1).amount w.blinding ∧
  nonidentity (c.assetGenerator w.asset)

/-- Complete component conjunction over one shared semantic witness. No
component conclusion is an input field of Witness. Public projection/encoding,
upstream interpretation contracts, source extraction and circuit soundness /
completeness are separate joins to this target. -/
def ComponentsSem (c : Crypto) (w : Witness) : Prop :=
  RegistrySem c w ∧ UserSem c w w.sender ∧ UserSem c w w.receiver ∧
  AuthorizationSem c w ∧ (∀ i, SpendSem c w i) ∧ (∀ i, OutputSem c w i) ∧
  VolumeSem c w ∧ RoutingSem c w ∧ EncryptionSem c w ∧ BalanceSem c w


def fieldsCanonical (fields : List Nat) : Prop := ∀ value ∈ fields, value < fieldModulus

def pathFields {depth : Nat} (siblings : Path depth) : List Nat :=
  (List.finRange depth).flatMap (fun level => (List.finRange 3).map (siblings level))

def userFields (u : User) : List Nat :=
  addressFields u.address ++ pointFields u.rnkDH ++
  [u.rnkCommitment, u.lifecycle, u.position] ++ pathFields u.siblings

def registryFields (l : AssetLeaf) : List Nat :=
  [l.value, l.nextIndex, l.nextValue, l.dailyLimit, l.routePolicy,
    l.ringID, l.policyID, l.permission, l.resource, l.audit.epoch, l.position] ++
  pointFields l.detection ++ pointFields l.ring ++ pointFields l.audit.payload ++
  pointFields l.audit.checking ++ pathFields l.siblings

def spendFields (s : Spend) : List Nat :=
  [s.blinding, s.amount, s.recovery, s.position, s.nullifier] ++ pathFields s.siblings

def recoveryFields (r : Recovery) : List Nat :=
  pointFields r.epk ++ [r.c2, r.salt, r.confirmation, r.encryptedAmount,
    r.encryptedBlinding, r.commitment, r.seed, r.randomizer]

def outputFields (o : Output) : List Nat :=
  [o.blinding, o.amount, o.noteCommitment] ++ recoveryFields o.recovery

def volumeFields (v : Volume) : List Nat :=
  [v.nullifier, v.commitment, v.dayStart, v.context, v.dayIndex, v.second,
    v.subject, v.prior, v.priorBlinding, v.priorCommitment, v.priorPosition,
    v.successor, v.successorBlinding] ++ pathFields v.priorSiblings

def encryptionFields (e : Encryption) : List Nat :=
  (List.finRange 4).flatMap (fun i =>
    let t := e.tiers i
    [e.detection i, e.policy i, e.salts i, t.ephemeral, t.c2, t.confirmation] ++
      pointFields t.epk ++ (List.finRange 3).map t.ciphertext) ++
  [e.timestamp, e.auditEpoch] ++ (List.finRange 2).flatMap (fun i =>
    [e.ownership i |>.randomness] ++ pointFields (e.ownership i).r ++ pointFields (e.ownership i).c)

/-- Every stored field representative, including inactive-branch auxiliaries,
path siblings and ciphertexts, is canonical. Native Booleans and finite indices
are already represented by their semantic types. -/
def CanonicalWitness (w : Witness) : Prop :=
  fieldsCanonical ([w.anchor, w.assetAnchor, w.userAnchor, w.asset, w.timestamp, w.nonce, w.blinding,
    w.paddingSeed, w.auth.nk, w.auth.ivk, w.auth.quotient, w.auth.randomizer,
    w.routing.regulatedPrecision, w.routing.unregulatedPrecision, w.routing.height,
    w.routing.parameterSet, w.routing.tags 0, w.routing.tags 1] ++
    pointFields w.auth.ak ++ pointFields w.auth.rk ++ registryFields w.registry ++
    userFields w.sender ++ userFields w.receiver ++
    (List.finRange 2).flatMap (fun i => spendFields (w.spends i) ++ outputFields (w.outputs i)) ++
    volumeFields w.volume ++ encryptionFields w.encryption)

/-- This codomain contract is required when interpreting the abstract operations
as the exact deployed field hash, encoding and group operations. It provides no
collision, discrete-log, commitment-binding or proof-system security theorem. -/
def CanonicalCrypto (c : Crypto) : Prop :=
  (∀ domain inputs, c.hash domain inputs < fieldModulus) ∧
  (∀ address i, c.addressWords address i < fieldModulus) ∧
  (∀ n p, CanonicalAffine (c.mul n p)) ∧
  (∀ p q, CanonicalAffine (c.add p q)) ∧
  (∀ asset, CanonicalAffine (c.assetGenerator asset)) ∧
  (∀ address, CanonicalAffine (c.fingerprint address)) ∧
  CanonicalAffine c.generator ∧ CanonicalAffine c.blindingGenerator ∧
  CanonicalAffine c.unregulatedDetection ∧ CanonicalAffine c.unregulatedRing ∧
  c.emptyPolicy < fieldModulus

/-- Exact independent ordered public data. The unusual tier order and
confirmation placement are intentional: this is Transfer's 64-field projection,
not encryption::Published::fields. -/
def publicFields (c : Crypto) (w : Witness) : List Nat :=
  let e := w.encryption
  let senderCore := e.tiers 0
  let senderExt := e.tiers 1
  let outputCore := e.tiers 2
  let outputExt := e.tiers 3
  let net := balance c w
  [w.auth.rk.x, w.auth.rk.y, w.anchor,
   (w.outputs 0).noteCommitment, (w.outputs 0).recovery.commitment,
   (w.outputs 1).noteCommitment, (w.outputs 1).recovery.commitment,
   net.x, net.y, w.routing.tags 0, w.routing.tags 1, w.routing.parameterSet,
   w.volume.nullifier, w.volume.commitment, w.volume.dayStart, w.volume.context,
   (w.spends 0).nullifier, (w.spends 1).nullifier, w.assetAnchor, w.userAnchor,
   e.detection 0, e.detection 1, e.detection 2, e.detection 3,
   senderCore.epk.x, senderCore.epk.y, senderCore.c2, senderCore.ciphertext 0,
   senderExt.epk.x, senderExt.epk.y, senderExt.c2,
   senderExt.ciphertext 0, senderExt.ciphertext 1, senderExt.ciphertext 2,
   outputCore.epk.x, outputCore.epk.y, outputCore.c2, outputCore.ciphertext 0,
   outputExt.epk.x, outputExt.epk.y, outputExt.c2,
   outputExt.ciphertext 0, outputExt.ciphertext 1, outputExt.ciphertext 2,
   w.timestamp, senderCore.confirmation, outputCore.confirmation,
   e.policy 0, e.policy 1, e.policy 2, e.policy 3,
   e.salts 0, e.salts 1, e.salts 2, e.salts 3, e.auditEpoch,
   (e.ownership 0).r.x, (e.ownership 0).r.y, (e.ownership 0).c.x, (e.ownership 0).c.y,
   (e.ownership 1).r.x, (e.ownership 1).r.y, (e.ownership 1).c.x, (e.ownership 1).c.y]

def TransferSem (c : Crypto) (w : Witness) : Prop :=
  CanonicalWitness w ∧ ComponentsSem c w ∧ fieldsCanonical (publicFields c w)

/-- This is a semantic relation target, not a claim that any actual circuit or
accepted transaction refines it. The committed value is the same witness
blinding used by the balance operation; the public value binds all 64 fields. -/
def TransferRelationSem (c : Crypto) (claimed committed : Nat) : Prop :=
  ∃ w, TransferSem c w ∧ committed = w.blinding ∧
    claimed = c.hash .transferStatement (publicFields c w)

theorem public_fields_length (c : Crypto) (w : Witness) :
    (publicFields c w).length = 64 := by rfl

set_option pp.all true in
#check @public_fields_length
#print axioms public_fields_length

end ShielddSecurity.TransferSem
