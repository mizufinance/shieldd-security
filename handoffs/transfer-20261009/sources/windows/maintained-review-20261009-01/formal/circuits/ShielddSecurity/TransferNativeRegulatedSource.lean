import ShielddSecurity.TransferStatement

set_option maxHeartbeats 150000

namespace ShielddSecurity.TransferNativeRegulatedSource

/-! The owned IndexedLeaf::from_policy projection, its policy-match check, and
Transfer's selected issuer/ring/RNK arguments. Whole route/audit values and
strings remain retained. Hash callbacks are arbitrary total functions; no
injectivity, registration or Merkle fact follows. Native getter/codec meaning,
full validation and compiled-row correspondence are separate obligations.
ActionWitness::nullifier_key does not call validate. -/

structure AssetParams (Point Routes Origin : Type) where
  issuer : Point
  dailyLimit : Nat
  routes : Routes
  origin : Option Origin

structure RingData (Point Audit : Type) where
  auditKeys : Audit
  ringKey : Point
  ringId : String
  policyId : String
  permission : String
  resource : String

structure Policy (Point Routes Origin Audit Key : Type) where
  params : AssetParams Point Routes Origin
  ring : RingData Point Audit
  registrationAuthority : Option Key
  seizureAuthority : Option Key

structure LeafParams (Q Point : Type) where
  issuer : Point
  dailyLimit : Nat
  routePolicy : Q

structure LeafRing (Q Point Audit : Type) where
  auditKeys : Audit
  ringKey : Point
  ringId : Q
  policyId : Q
  permission : Q
  resource : Q

structure Leaf (Q Point Audit : Type) where
  value : Q
  nextIndex : Nat
  nextValue : Q
  params : LeafParams Q Point
  ring : LeafRing Q Point Audit

structure Hashes (Q Point Routes Origin : Type) where
  string : String → Q
  routes : AssetParams Point Routes Origin → Q

def fromPolicy {Q Point Routes Origin Audit Key : Type}
    (hashes : Hashes Q Point Routes Origin) (value : Q) (nextIndex : Nat) (nextValue : Q)
    (policy : Policy Point Routes Origin Audit Key) : Leaf Q Point Audit :=
  { value := value, nextIndex := nextIndex, nextValue := nextValue
    params := ⟨policy.params.issuer, policy.params.dailyLimit, hashes.routes policy.params⟩
    ring := ⟨policy.ring.auditKeys, policy.ring.ringKey, hashes.string policy.ring.ringId,
      hashes.string policy.ring.policyId, hashes.string policy.ring.permission, hashes.string policy.ring.resource⟩ }

noncomputable def checkPolicy {Q Point Routes Origin Audit Key : Type}
    (hashes : Hashes Q Point Routes Origin) (leaf : Leaf Q Point Audit)
    (policy : Policy Point Routes Origin Audit Key) : Option (Policy Point Routes Origin Audit Key) := by
  classical
  exact if leaf = fromPolicy hashes leaf.value leaf.nextIndex leaf.nextValue policy
    then some policy else none

theorem checked_policy_fields {Q Point Routes Origin Audit Key : Type}
    (hashes : Hashes Q Point Routes Origin) (leaf : Leaf Q Point Audit)
    (input accepted : Policy Point Routes Origin Audit Key)
    (checked : checkPolicy hashes leaf input = some accepted) :
    accepted = input ∧ leaf.params.issuer = accepted.params.issuer ∧
      leaf.ring.ringKey = accepted.ring.ringKey ∧ leaf.ring.auditKeys = accepted.ring.auditKeys := by
  classical
  by_cases same : leaf = fromPolicy hashes leaf.value leaf.nextIndex leaf.nextValue input
  · have identity : input = accepted :=
      Option.some.inj (by simpa only [checkPolicy, if_pos same] using checked)
    subst accepted
    exact ⟨rfl, congrArg (fun value => value.params.issuer) same,
      congrArg (fun value => value.ring.ringKey) same, congrArg (fun value => value.ring.auditKeys) same⟩
  · simp only [checkPolicy, if_neg same] at checked
    cases checked

structure Selected (Point : Type) where
  issuer : Point
  ring : Point

def selected {Q Point Audit : Type} (leaf : Leaf Q Point Audit) (regulated : Bool)
    (fixedIssuer fixedRing : Point) : Selected Point :=
  if regulated then ⟨leaf.params.issuer, leaf.ring.ringKey⟩ else ⟨fixedIssuer, fixedRing⟩

theorem regulated_selected_keys {Q Point Routes Origin Audit Key : Type}
    (hashes : Hashes Q Point Routes Origin) (leaf : Leaf Q Point Audit)
    (input accepted : Policy Point Routes Origin Audit Key) (fixedIssuer fixedRing : Point)
    (checked : checkPolicy hashes leaf input = some accepted) :
    selected leaf true fixedIssuer fixedRing = ⟨accepted.params.issuer, accepted.ring.ringKey⟩ := by
  obtain ⟨_, issuer, ring, _⟩ := checked_policy_fields hashes leaf input accepted checked
  change (⟨leaf.params.issuer, leaf.ring.ringKey⟩ : Selected Point) = _
  rw [issuer, ring]

theorem unregulated_selected_keys {Q Point Audit : Type}
    (leaf : Leaf Q Point Audit) (fixedIssuer fixedRing : Point) :
    selected leaf false fixedIssuer fixedRing = ⟨fixedIssuer, fixedRing⟩ := rfl

structure Coordinates (Q Point : Type) where
  x : Point → Q
  y : Point → Q

def rnkInputs {Q Point : Type} (coordinates : Coordinates Q Point)
    (dh diversified transmission : Point) (asset : Q) (ring : Point) : List Q :=
  [coordinates.x dh, coordinates.y dh, coordinates.x diversified, coordinates.y diversified,
   coordinates.x transmission, coordinates.y transmission, asset, coordinates.x ring, coordinates.y ring]

theorem regulated_hash_arguments {Q Point Routes Origin Audit Key : Type}
    (hashes : Hashes Q Point Routes Origin) (coordinates : Coordinates Q Point)
    (leaf : Leaf Q Point Audit) (input accepted : Policy Point Routes Origin Audit Key)
    (fixedIssuer fixedRing dh diversified transmission : Point) (asset : Q)
    (checked : checkPolicy hashes leaf input = some accepted) :
    rnkInputs coordinates dh diversified transmission asset
        (selected leaf true fixedIssuer fixedRing).ring =
      rnkInputs coordinates dh diversified transmission asset accepted.ring.ringKey := by
  rw [regulated_selected_keys hashes leaf input accepted fixedIssuer fixedRing checked]

def effectiveNk {Q : Type} (regulated : Bool) (rnk walletNk : Q) : Q :=
  if regulated then rnk else walletNk

theorem effective_nk_branches {Q : Type} (rnk walletNk : Q) :
    effectiveNk true rnk walletNk = rnk ∧ effectiveNk false rnk walletNk = walletNk := ⟨rfl, rfl⟩

set_option pp.all true in
#check @checked_policy_fields
#print axioms checked_policy_fields
set_option pp.all true in
#check @regulated_selected_keys
#print axioms regulated_selected_keys
set_option pp.all true in
#check @unregulated_selected_keys
#print axioms unregulated_selected_keys
set_option pp.all true in
#check @regulated_hash_arguments
#print axioms regulated_hash_arguments
set_option pp.all true in
#check @effective_nk_branches
#print axioms effective_nk_branches

end ShielddSecurity.TransferNativeRegulatedSource
