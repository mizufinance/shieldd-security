import ShielddSecurity.ShielddNativeRegulatedLegality

set_option maxHeartbeats 250000

namespace ShielddSecurity.ShielddNativePolicyDecoder

open GroupByteCodec TransferNativeRegulatedSource ShielddNativeRegulatedLegality
  ShielddNativeAddressLegality

variable {F : Type} [Field F]
  {E S R K Q Signing J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

def byteAt (raw : List Byte) (offset : Nat) : Byte :=
  raw[offset]?.getD ⟨0,by decide⟩

def pointBytes (raw : List Byte) (offset : Nat) : Bytes :=
  fun index => byteAt raw (offset + index.val)

def littleInteger (raw : List Byte) (offset count : Nat) : Nat :=
  ((List.range count).map (fun index => (byteAt raw (offset+index)).val * 256^index)).sum

/-- encoding::point performs canonical subgroup decoding and re-encoding.
Identity is permitted here; the policy's final validation rejects it. -/
noncomputable def point
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (bytes : Bytes) : Option S := by
  classical
  exact match upstream.decodePoint bytes with
  | none => none
  | some value => if upstream.encode (upstream.promote value) = bytes then some value else none

structure Prefix (S : Type) where
  issuer : S
  dailyLimit : Nat
  ring : S
  audit : AuditKeys S

def header (raw : List Byte) : Prop :=
  157 ≤ raw.length ∧ (raw.take 4).map Fin.val = [65,83,80,53] ∧
    (byteAt raw 84).val = 1

/-- The complete point-bearing ASP5 prefix. The checked minimum length makes
all four 32-byte reads and both LE integer reads in bounds. AuditKeys::from_bytes
uses suite 1 and its two nonidentity decoders. No suffix callback can supply
issuer, ring, audit keys, daily limit or epoch. -/
noncomputable def parsePrefix
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (raw : List Byte) : Option (Prefix S) := by
  classical
  exact if header raw then do
    let issuer ← point upstream (pointBytes raw 4)
    let ring ← point upstream (pointBytes raw 52)
    let payload ← ShielddNativeSdk.nonidentity upstream (pointBytes raw 93)
    let checking ← ShielddNativeSdk.nonidentity upstream (pointBytes raw 125)
    pure ⟨issuer,littleInteger raw 36 16,ring,⟨littleInteger raw 85 8,payload,checking⟩⟩
  else none

theorem prefix_fields
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (raw : List Byte) (value : Prefix S)
    (accepted : parsePrefix upstream raw = some value) :
    header raw ∧ point upstream (pointBytes raw 4) = some value.issuer ∧
      point upstream (pointBytes raw 52) = some value.ring ∧
      ShielddNativeSdk.nonidentity upstream (pointBytes raw 93) = some value.audit.payload ∧
      ShielddNativeSdk.nonidentity upstream (pointBytes raw 125) = some value.audit.checking ∧
      value.dailyLimit = littleInteger raw 36 16 ∧ value.audit.epoch = littleInteger raw 85 8 := by
  classical
  by_cases valid : header raw
  · cases issuerRead : point upstream (pointBytes raw 4) with
    | none => simp [parsePrefix,valid,issuerRead] at accepted
    | some issuer =>
      cases ringRead : point upstream (pointBytes raw 52) with
      | none => simp [parsePrefix,valid,issuerRead,ringRead] at accepted
      | some ring =>
        cases payloadRead : ShielddNativeSdk.nonidentity upstream (pointBytes raw 93) with
        | none => simp [parsePrefix,valid,issuerRead,ringRead,payloadRead] at accepted
        | some payload =>
          cases checkingRead : ShielddNativeSdk.nonidentity upstream (pointBytes raw 125) with
          | none => simp [parsePrefix,valid,issuerRead,ringRead,payloadRead,checkingRead] at accepted
          | some checking =>
            have same : (⟨issuer,littleInteger raw 36 16,ring,
                ⟨littleInteger raw 85 8,payload,checking⟩⟩ : Prefix S) = value :=
              Option.some.inj (by simpa [parsePrefix,valid,issuerRead,ringRead,payloadRead,checkingRead] using accepted)
            subst value
            exact ⟨valid,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · simp [parsePrefix,valid] at accepted

/-- The suffix type deliberately has no point-bearing prefix fields. Its
callback remains an explicit UTF-8/route/optional-authority parsing boundary;
this module does not certify that callback or the complete storage decoder. -/
structure Tail (Routes Origin Key : Type) where
  routes : Routes
  origin : Option Origin
  ringId : String
  policyId : String
  permission : String
  resource : String
  registration : Option Key
  seizure : Option Key

def assemble {Routes Origin Key : Type} (prefixValue : Prefix S)
    (tail : Tail Routes Origin Key) : Policy S Routes Origin (AuditKeys S) Key :=
  { params := ⟨prefixValue.issuer,prefixValue.dailyLimit,tail.routes,tail.origin⟩
    ring := ⟨prefixValue.audit,prefixValue.ring,tail.ringId,tail.policyId,tail.permission,tail.resource⟩
    registrationAuthority := tail.registration
    seizureAuthority := tail.seizure }

noncomputable def body {Routes Origin Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (decodeTail : List Byte → Option (Tail Routes Origin Key)) (raw : List Byte) :
    Option (Policy S Routes Origin (AuditKeys S) Key) := do
  let prefixValue ← parsePrefix upstream raw
  let tail ← decodeTail (raw.drop 157)
  pure (assemble prefixValue tail)

noncomputable def fromBytes {Routes Origin Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (authorityCheck : Key → Bool) (decodeTail : List Byte → Option (Tail Routes Origin Key))
    (raw : List Byte) : Option (Policy S Routes Origin (AuditKeys S) Key) :=
  decodePolicy upstream authorityCheck (body upstream decodeTail) raw

theorem body_fields {Routes Origin Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (decodeTail : List Byte → Option (Tail Routes Origin Key)) (raw : List Byte)
    (policy : Policy S Routes Origin (AuditKeys S) Key)
    (accepted : body upstream decodeTail raw = some policy) :
    ∃ prefixValue tail, parsePrefix upstream raw = some prefixValue ∧
      decodeTail (raw.drop 157) = some tail ∧ policy = assemble prefixValue tail := by
  cases prefixRead : parsePrefix upstream raw with
  | none => simp [body,prefixRead] at accepted
  | some prefixValue =>
    cases tailRead : decodeTail (raw.drop 157) with
    | none => simp [body,prefixRead,tailRead] at accepted
    | some tail =>
      have same : assemble prefixValue tail = policy :=
        Option.some.inj (by simpa [body,prefixRead,tailRead] using accepted)
      exact ⟨prefixValue,tail,rfl,rfl,same.symm⟩

private theorem validated_original {Routes Origin Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (authorityCheck : Key → Bool)
    (input output : Policy S Routes Origin (AuditKeys S) Key)
    (accepted : validateCryptoKeys upstream authorityCheck input = some output) :
    output = input := by
  unfold validateCryptoKeys at accepted
  repeat' first | (split at accepted) | (cases accepted)
  rfl

theorem decoded_fields {Routes Origin Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (authorityCheck : Key → Bool) (decodeTail : List Byte → Option (Tail Routes Origin Key))
    (raw : List Byte) (policy : Policy S Routes Origin (AuditKeys S) Key)
    (accepted : fromBytes upstream authorityCheck decodeTail raw = some policy) :
    header raw ∧ point upstream (pointBytes raw 4) = some policy.params.issuer ∧
      point upstream (pointBytes raw 52) = some policy.ring.ringKey ∧
      ShielddNativeSdk.nonidentity upstream (pointBytes raw 93) = some policy.ring.auditKeys.payload ∧
      ShielddNativeSdk.nonidentity upstream (pointBytes raw 125) = some policy.ring.auditKeys.checking := by
  cases bodyRead : body upstream decodeTail raw with
  | none => simp [fromBytes,decodePolicy,bodyRead] at accepted
  | some input =>
    have validated : validateCryptoKeys upstream authorityCheck input = some policy := by
      simpa only [fromBytes,decodePolicy,bodyRead] using accepted
    have same := validated_original upstream authorityCheck input policy validated
    obtain ⟨prefixValue,tail,prefixRead,_,assembled⟩ := body_fields upstream decodeTail raw input bodyRead
    obtain ⟨valid,issuer,ring,payload,checking,_,_⟩ := prefix_fields upstream raw prefixValue prefixRead
    rw [same,assembled]
    exact ⟨valid,issuer,ring,payload,checking⟩

theorem decoded_keys_legal {Routes Origin Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (authorityCheck : Key → Bool) (decodeTail : List Byte → Option (Tail Routes Origin Key))
    (raw : List Byte) (policy : Policy S Routes Origin (AuditKeys S) Key)
    (accepted : fromBytes upstream authorityCheck decodeTail raw = some policy) :
    LegalPoint upstream policy.params.issuer ∧ LegalPoint upstream policy.ring.ringKey :=
  policy_decoder_legal upstream authorityCheck (body upstream decodeTail) raw policy accepted

theorem checked_leaf_keys {Routes Origin Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (authorityCheck : Key → Bool) (decodeTail : List Byte → Option (Tail Routes Origin Key))
    (raw : List Byte) (policy : Policy S Routes Origin (AuditKeys S) Key)
    (hashes : Hashes Q S Routes Origin) (leaf : Leaf Q S (AuditKeys S))
    (decoded : fromBytes upstream authorityCheck decodeTail raw = some policy)
    (matched : checkPolicy hashes leaf policy = some policy) :
    leaf.params.issuer = policy.params.issuer ∧ leaf.ring.ringKey = policy.ring.ringKey ∧
      leaf.ring.auditKeys = policy.ring.auditKeys ∧
      LegalPoint upstream leaf.params.issuer ∧ LegalPoint upstream leaf.ring.ringKey := by
  obtain ⟨_,issuer,ring,audit⟩ := checked_policy_fields hashes leaf policy policy matched
  have legal := checked_leaf_keys_legal upstream authorityCheck (body upstream decodeTail)
    raw policy hashes leaf decoded matched
  exact ⟨issuer,ring,audit,legal⟩

set_option pp.all true in
#check @prefix_fields
#print axioms prefix_fields
set_option pp.all true in
#check @body_fields
#print axioms body_fields
set_option pp.all true in
#check @decoded_fields
#print axioms decoded_fields
set_option pp.all true in
#check @decoded_keys_legal
#print axioms decoded_keys_legal
set_option pp.all true in
#check @checked_leaf_keys
#print axioms checked_leaf_keys

end ShielddSecurity.ShielddNativePolicyDecoder
