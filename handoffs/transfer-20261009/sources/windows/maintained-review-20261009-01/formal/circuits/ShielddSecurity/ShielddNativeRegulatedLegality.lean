import ShielddSecurity.ShielddNativeAddressLegality
import ShielddSecurity.TransferNativeRegulatedSource

set_option maxHeartbeats 250000

namespace ShielddSecurity.ShielddNativeRegulatedLegality

open ShielddNativeAddress ShielddNativeAddressLegality TransferNativeRegulatedSource

variable {F : Type} [Field F]
  {E S R K Q Signing J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

structure AuditKeys (S : Type) where
  epoch : Nat
  payload : S
  checking : S

/-- The exact owned regulated derivation sequence: views_address, ring and
DH-base identity rejection, native key agreement, canonical nonidentity shared
decode, then the nine ordered Poseidon inputs. Agreement and hash are arbitrary
global callbacks, not successful-output or cryptographic premises. Their
instantiation and the native byte decoder/source-object relation remain visible
source obligations. In particular DH base and address diversified are distinct. -/
noncomputable def deriveRegulated [DecidableEq S]
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream)
    (agreement : Secret → S → Option GroupByteCodec.Bytes)
    (hash : Nat → List Q → Q) (secret : Secret) (address : Address S)
    (asset : Q) (ring dhBase : S) : Option Q := by
  classical
  exact if viewsAddress upstream primitives secret address then
    if upstream.isIdentity ring then none else
    if upstream.isIdentity dhBase then none else
    match agreement secret dhBase with
    | none => none
    | some bytes => match ShielddNativeSdk.nonidentity upstream bytes with
      | none => none
      | some shared => some (hash 17 (rnkInputs
          ⟨ShielddNativeSdk.coordinateX upstream,ShielddNativeSdk.coordinateY upstream⟩
          shared address.diversified address.transmission.point asset ring))
  else none

private theorem checked_point_legal
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (point : S) (checked : upstream.isIdentity point = false) : LegalPoint upstream point := by
  refine ⟨upstream.subgroup point,?_⟩
  intro zero
  have identity := (upstream.identityReflects point).mpr zero
  rw [checked] at identity
  cases identity

theorem regulated_derivation_legal [DecidableEq S]
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream)
    (agreement : Secret → S → Option GroupByteCodec.Bytes)
    (hash : Nat → List Q → Q) (secret : Secret) (address : Address S)
    (asset : Q) (ring dhBase : S) (output : Q)
    (accepted : deriveRegulated upstream primitives agreement hash secret address asset ring dhBase = some output) :
    LegalPoint upstream ring ∧ LegalPoint upstream dhBase := by
  classical
  cases viewed : viewsAddress upstream primitives secret address with
  | false =>
      simp only [deriveRegulated,viewed,Bool.false_eq_true,ite_false] at accepted
      cases accepted
  | true =>
      cases ringIdentity : upstream.isIdentity ring with
      | true =>
          simp only [deriveRegulated,viewed,ringIdentity,ite_true] at accepted
          cases accepted
      | false =>
          cases dhIdentity : upstream.isIdentity dhBase with
          | true =>
              simp only [deriveRegulated,viewed,ringIdentity,dhIdentity,Bool.false_eq_true,ite_true,ite_false] at accepted
              cases accepted
          | false =>
              exact ⟨checked_point_legal upstream ring ringIdentity,
                checked_point_legal upstream dhBase dhIdentity⟩

/-- validate_crypto_keys checks both audit keys, then issuer and ring, then
the two optional authority keys. Optional authority verification is retained
as a global predicate; no authority security conclusion is derived here. -/
def authorityValid {Key : Type} (check : Key → Bool) (authority : Option Key) : Bool :=
  match authority with
  | none => true
  | some key => check key

def validateCryptoKeys {Routes Origin Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (authorityCheck : Key → Bool) (policy : Policy S Routes Origin (AuditKeys S) Key) :
    Option (Policy S Routes Origin (AuditKeys S) Key) :=
  if upstream.isIdentity policy.ring.auditKeys.payload then none else
  if upstream.isIdentity policy.ring.auditKeys.checking then none else
  if upstream.isIdentity policy.params.issuer then none else
  if upstream.isIdentity policy.ring.ringKey then none else
  if authorityValid authorityCheck policy.registrationAuthority then
    if authorityValid authorityCheck policy.seizureAuthority then some policy else none
  else none

/-- AssetPolicy::from_bytes and protobuf conversion first construct the full
policy from the actual decoded fields, then run validate_crypto_keys before
returning. The complete parser is an arbitrary global callback here: these
lemmas prove the owned final guards, not parser fidelity from a byte hash. -/
def decodePolicy {Raw Routes Origin Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (authorityCheck : Key → Bool)
    (decodeBody : Raw → Option (Policy S Routes Origin (AuditKeys S) Key))
    (raw : Raw) : Option (Policy S Routes Origin (AuditKeys S) Key) :=
  match decodeBody raw with
  | none => none
  | some policy => validateCryptoKeys upstream authorityCheck policy

private theorem validated_keys_legal {Routes Origin Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (authorityCheck : Key → Bool)
    (policy acceptedPolicy : Policy S Routes Origin (AuditKeys S) Key)
    (accepted : validateCryptoKeys upstream authorityCheck policy = some acceptedPolicy) :
    acceptedPolicy = policy ∧ LegalPoint upstream policy.params.issuer ∧
      LegalPoint upstream policy.ring.ringKey := by
  cases payload : upstream.isIdentity policy.ring.auditKeys.payload with
  | true => simp only [validateCryptoKeys,payload,ite_true] at accepted; cases accepted
  | false =>
      cases checking : upstream.isIdentity policy.ring.auditKeys.checking with
      | true =>
          simp only [validateCryptoKeys,payload,checking,Bool.false_eq_true,ite_false,ite_true] at accepted
          cases accepted
      | false =>
          cases issuer : upstream.isIdentity policy.params.issuer with
          | true =>
              simp only [validateCryptoKeys,payload,checking,issuer,Bool.false_eq_true,ite_false,ite_true] at accepted
              cases accepted
          | false =>
              cases ring : upstream.isIdentity policy.ring.ringKey with
              | true =>
                  simp only [validateCryptoKeys,payload,checking,issuer,ring,Bool.false_eq_true,ite_false,ite_true] at accepted
                  cases accepted
              | false =>
                  cases registration : authorityValid authorityCheck policy.registrationAuthority with
                  | false =>
                      simp only [validateCryptoKeys,payload,checking,issuer,ring,registration,Bool.false_eq_true,ite_false] at accepted
                      cases accepted
                  | true =>
                      cases seizure : authorityValid authorityCheck policy.seizureAuthority with
                      | false =>
                          simp only [validateCryptoKeys,payload,checking,issuer,ring,registration,seizure,Bool.false_eq_true,ite_false,ite_true] at accepted
                          cases accepted
                      | true =>
                          have same : policy = acceptedPolicy := Option.some.inj (by
                            simpa only [validateCryptoKeys,payload,checking,issuer,ring,registration,seizure,Bool.false_eq_true,ite_false,ite_true] using accepted)
                          exact ⟨same.symm,checked_point_legal upstream _ issuer,checked_point_legal upstream _ ring⟩

theorem policy_decoder_legal {Raw Routes Origin Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (authorityCheck : Key → Bool)
    (decodeBody : Raw → Option (Policy S Routes Origin (AuditKeys S) Key))
    (raw : Raw) (policy : Policy S Routes Origin (AuditKeys S) Key)
    (accepted : decodePolicy upstream authorityCheck decodeBody raw = some policy) :
    LegalPoint upstream policy.params.issuer ∧ LegalPoint upstream policy.ring.ringKey := by
  cases decoded : decodeBody raw with
  | none => simp only [decodePolicy,decoded] at accepted; cases accepted
  | some input =>
      have guarded : validateCryptoKeys upstream authorityCheck input = some policy := by
        simpa only [decodePolicy,decoded] using accepted
      obtain ⟨same,issuer,ring⟩ := validated_keys_legal upstream authorityCheck input policy guarded
      rw [same]
      exact ⟨issuer,ring⟩

/-- Only the exact owned policy-to-leaf match transports the validated issuer
and ring to the selected regulated inputs. Membership alone cannot do this;
IndexedLeaf's point parser explicitly permits identity. -/
theorem checked_leaf_keys_legal {Raw Routes Origin Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (authorityCheck : Key → Bool)
    (decodeBody : Raw → Option (Policy S Routes Origin (AuditKeys S) Key))
    (raw : Raw) (policy : Policy S Routes Origin (AuditKeys S) Key)
    (hashes : Hashes Q S Routes Origin) (leaf : Leaf Q S (AuditKeys S))
    (decoded : decodePolicy upstream authorityCheck decodeBody raw = some policy)
    (matched : checkPolicy hashes leaf policy = some policy) :
    LegalPoint upstream leaf.params.issuer ∧ LegalPoint upstream leaf.ring.ringKey := by
  have guarded := policy_decoder_legal upstream authorityCheck decodeBody raw policy decoded
  obtain ⟨_,issuer,ring,_⟩ := checked_policy_fields hashes leaf policy policy matched
  rw [issuer,ring]
  exact guarded

set_option pp.all true in
#check @regulated_derivation_legal
#print axioms regulated_derivation_legal
set_option pp.all true in
#check @policy_decoder_legal
#print axioms policy_decoder_legal
set_option pp.all true in
#check @checked_leaf_keys_legal
#print axioms checked_leaf_keys_legal

end ShielddSecurity.ShielddNativeRegulatedLegality
