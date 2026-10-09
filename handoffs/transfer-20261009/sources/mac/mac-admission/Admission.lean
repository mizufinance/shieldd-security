import Lean.Elab.Tactic.Omega

/- Original narrow model, runtime 844389ee069e1fb2e576708842d0b389b4d9a44a.
   Natural numbers label decoded values/keys; they are NOT BLS/Jubjub arithmetic.
   The codec, backend, circuit refinement and collision premises are explicit.
   See source-contract.txt for the manual correspondence and its open boundaries. -/
set_option maxHeartbeats 400000
namespace MacAdmission

structure Envelope where
  byteLength : Nat
  suite : Nat
  family : Nat
  relation : Nat
  publics : List Nat
  commitments : Nat
  remainder : Nat
  canonical : Prop

structure Key where
  relation : Nat
  identity : Nat

structure Decoded (suite : Nat) (e : Envelope) : Prop where
  length : e.byteLength = 244
  suiteBound : e.suite = suite
  familyKnown : e.family ∈ [1, 2, 3, 4, 5, 6, 9]
  publicCount : e.publics.length = 1
  commitmentCount : e.commitments = 1
  exhausted : e.remainder = 0
  canonicalEncoding : e.canonical

structure Accepted (suite family statement : Nat) (keyFor : Nat → Key)
    (backend : Key → Envelope → Prop) (e : Envelope) : Prop where
  decoded : Decoded suite e
  familyBound : e.family = family
  relationBound : e.relation = (keyFor family).relation
  statementBound : e.publics = [statement]
  commitmentCount : e.commitments = 1
  verified : backend (keyFor family) e

theorem accepted_context (h : Accepted suite family statement keyFor backend e) :
    e.suite = suite ∧ e.family = family ∧
    e.relation = (keyFor family).relation ∧ e.publics = [statement] ∧
    e.commitments = 1 ∧ e.canonical ∧ e.remainder = 0 :=
  ⟨h.decoded.suiteBound, h.familyBound, h.relationBound, h.statementBound,
    h.commitmentCount, h.decoded.canonicalEncoding, h.decoded.exhausted⟩

-- Backend/circuit joins are hypotheses, not added axioms or established results.
structure Assignment where
  publics : List Nat
  committed : List Nat
  balanceBlinding : Nat
  inputs : Int
  outputs : Int
  signedNet : Int

def BackendSound (backend : Key → Envelope → Prop)
    (satisfies : Nat → Assignment → Prop)
    (opensClaim : Envelope → Assignment → Prop) : Prop :=
  ∀ k e, backend k e → ∃ z, satisfies k.relation z ∧
    z.publics = e.publics ∧ opensClaim e z

def TransferRefinement (satisfies : Nat → Assignment → Prop) (relation : Nat) : Prop :=
  ∀ z, satisfies relation z →
    z.committed = [z.balanceBlinding] ∧ z.signedNet = z.inputs - z.outputs

theorem conditional_relation_join
    (h : Accepted suite 1 statement keyFor backend e)
    (sound : BackendSound backend satisfies opensClaim)
    (refine : TransferRefinement satisfies (keyFor 1).relation) :
    ∃ z, satisfies (keyFor 1).relation z ∧ z.publics = [statement] ∧
      opensClaim e z ∧ z.committed = [z.balanceBlinding] ∧
      z.signedNet = z.inputs - z.outputs := by
  obtain ⟨z, hz, hp, opening⟩ := sound (keyFor 1) e h.verified
  obtain ⟨hc, hs⟩ := refine z hz
  exact ⟨z, hz, hp.trans h.statementBound, opening, hc, hs⟩

-- Exact structural projection: one chosen digest and one chosen blinding value.
def selectedLayout (digest blinding : Nat) : List Nat × List (List Nat) :=
  ([digest], [[blinding]])

theorem same_selected_blinding (digest blinding : Nat) :
    (selectedLayout digest blinding).1 = [digest] ∧
    (selectedLayout digest blinding).2 = [[blinding]] := ⟨rfl, rfl⟩

structure Item where
  family : Nat
  statement : Nat
  proofBytes : List Nat
  deriving DecidableEq

structure Verified where
  registry : Nat
  item : Item

def Binds (v : Verified) (family : Nat) (request : Item) : Prop :=
  family = v.item.family ∧ v.item = request

theorem capability_binds_exact_item (h : Binds v family request) :
    v.item.family = family ∧ v.item.statement = request.statement ∧
    v.item.proofBytes = request.proofBytes := by
  exact ⟨h.1.symm, congrArg Item.statement h.2, congrArg Item.proofBytes h.2⟩

theorem capability_rejects_changed_item (different : v.item ≠ request) :
    ¬ Binds v family request := fun h => different h.2

-- Direct ensure_binds does not inspect registry; the parent artifact does.
def ParentBinds (registry : Nat) (v : Verified) (family : Nat) (request : Item) : Prop :=
  v.registry = registry ∧ Binds v family request

theorem caller_registry_closure (h : ParentBinds registry v family request) :
    v.registry = registry ∧ v.item = request := ⟨h.1, h.2.2⟩

theorem direct_binds_does_not_bind_registry :
    ∃ v : Verified, Binds v 1 ⟨1, 7, [9]⟩ ∧ v.registry ≠ 2 := by
  exact ⟨⟨3, ⟨1, 7, [9]⟩⟩, ⟨rfl, rfl⟩, by decide⟩

structure Action where
  anchor : Nat
  kind : Nat
  projectedTail : List Nat
  effectData : List Nat
  proofBytes : List Nat
  signature : Nat
  deriving DecidableEq

structure Context where
  anchor : Nat
  effectHash : Nat
  deriving DecidableEq

-- This models inclusion, not the 64-field order or Rust encoders. The exact
-- order, point representation and projections remain correspondence obligations.
def fields (a : Action) (c : Context) : List Nat :=
  c.anchor :: a.kind :: a.projectedTail

def extracted (digestFn : List Nat → Nat) (a : Action) (c : Context) : Item :=
  ⟨1, digestFn (fields a c), a.proofBytes⟩

structure Stateless (auth : Action → Nat → Prop) (shape lengths : Action → Prop)
    (a : Action) (c : Context) (expected : Nat) : Prop where
  anchorBound : a.anchor = c.anchor
  bodyShape : shape a
  contextBound : a.kind = expected
  authorized : auth a c.effectHash
  lengthsBound : lengths a

structure Validated where
  item : Item
  kind : Nat

def ValidateProduces (digestFn : List Nat → Nat) (auth : Action → Nat → Prop)
    (shape lengths : Action → Prop) (preconditions : Action → Prop)
    (a : Action) (c : Context) (v : Verified) (expected : Nat)
    (receipt : Validated) : Prop :=
  Stateless auth shape lengths a c expected ∧ Binds v 1 (extracted digestFn a c) ∧
  preconditions a ∧ receipt.item = extracted digestFn a c ∧ receipt.kind = expected

def ExecuteAdmits (digestFn : List Nat → Nat) (auth : Action → Nat → Prop)
    (shape lengths : Action → Prop) (a : Action) (c : Context)
    (receipt : Validated) : Prop :=
  Stateless auth shape lengths a c receipt.kind ∧ receipt.item = extracted digestFn a c

theorem validation_execution_chain
    (validated : ValidateProduces digestFn auth shape lengths pre a₀ c₀ v expected receipt)
    (executed : ExecuteAdmits digestFn auth shape lengths a₁ c₁ receipt) :
    extracted digestFn a₀ c₀ = extracted digestFn a₁ c₁ ∧
    a₀.kind = a₁.kind ∧ a₁.anchor = c₁.anchor ∧ auth a₁ c₁.effectHash ∧ pre a₀ := by
  obtain ⟨s₀, _, pre₀, item₀, kind₀⟩ := validated
  obtain ⟨s₁, item₁⟩ := executed
  exact ⟨item₀.symm.trans item₁,
    s₀.contextBound.trans (kind₀.symm.trans s₁.contextBound.symm),
    s₁.anchorBound, s₁.authorized, pre₀⟩

-- A pair-specific collision exclusion avoids asserting globally injective hashes.
def NoCollisionFor (digestFn : List Nat → Nat) (x y : List Nat) : Prop :=
  digestFn x = digestFn y → x = y

theorem exact_projected_fields_under_collision_exclusion
    (eq : extracted digestFn a₀ c₀ = extracted digestFn a₁ c₁)
    (collision : NoCollisionFor digestFn (fields a₀ c₀) (fields a₁ c₁)) :
    fields a₀ c₀ = fields a₁ c₁ := by
  exact collision (congrArg Item.statement eq)

theorem changed_anchor_rejects_reuse_under_collision_exclusion
    (neq : c₀.anchor ≠ c₁.anchor)
    (collision : NoCollisionFor digestFn (fields a₀ c₀) (fields a₁ c₁)) :
    extracted digestFn a₀ c₀ ≠ extracted digestFn a₁ c₁ := by
  intro eq
  have f := exact_projected_fields_under_collision_exclusion eq collision
  have anchorEq : c₀.anchor = c₁.anchor := List.cons.inj f |>.1
  exact neq anchorEq

-- Literal full action/context equality is deliberately not a capability claim.
theorem projection_does_not_bind_effect_hash :
    ∃ a c₀ c₁, c₀ ≠ c₁ ∧ extracted (fun _ => 7) a c₀ = extracted (fun _ => 7) a c₁ := by
  exact ⟨⟨5, 1, [4], [8], [9], 10⟩, ⟨5, 20⟩, ⟨5, 21⟩,
    by decide, rfl⟩

theorem projection_does_not_bind_full_action :
    ∃ a₀ a₁ c, a₀ ≠ a₁ ∧
      extracted (fun xs => xs.length) a₀ c = extracted (fun xs => xs.length) a₁ c := by
  exact ⟨⟨5, 1, [4], [8], [9], 10⟩, ⟨5, 1, [4], [11], [9], 12⟩,
    ⟨5, 20⟩, by decide, rfl⟩

-- Authority must be freshly checked against the caller's current effect digestFn.
theorem execution_rechecks_authorization
    (h : ExecuteAdmits digestFn auth shape lengths a c receipt) : auth a c.effectHash :=
  h.1.authorized

-- A concrete two-state control: the earlier precondition was true and the same
-- receipt still admits execution after that predicate becomes false. Actual
-- state transitions/stability and nullify_all are separate runtime obligations.
def preAt (state : Nat) (_ : Action) : Prop := state = 0

theorem validation_execution_does_not_imply_fresh_state :
    ∃ a c v receipt,
      ValidateProduces (fun xs => xs.length) (fun _ _ => True)
        (fun _ => True) (fun _ => True) (preAt 0) a c v 1 receipt ∧
      ExecuteAdmits (fun xs => xs.length) (fun _ _ => True)
        (fun _ => True) (fun _ => True) a c receipt ∧ ¬ preAt 1 a := by
  let a : Action := ⟨5, 1, [4], [8], [9], 10⟩
  let c : Context := ⟨5, 20⟩
  let item := extracted (fun xs => xs.length) a c
  refine ⟨a, c, ⟨2, item⟩, ⟨item, 1⟩, ?_⟩
  have stateless : Stateless (fun _ _ => True) (fun _ => True)
      (fun _ => True) a c 1 := ⟨rfl, trivial, rfl, trivial, trivial⟩
  exact ⟨⟨stateless, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩,
    ⟨stateless, rfl⟩, by simp [preAt]⟩

-- Signed action net balance need not be zero.
theorem nonzero_signed_balance_is_consistent :
    ∃ inputs outputs net : Int, inputs ≥ 0 ∧ outputs ≥ 0 ∧
      net = inputs - outputs ∧ net ≠ 0 := by
  exact ⟨3, 5, -2, by omega⟩

#print axioms accepted_context
#print axioms conditional_relation_join
#print axioms same_selected_blinding
#print axioms capability_binds_exact_item
#print axioms capability_rejects_changed_item
#print axioms caller_registry_closure
#print axioms direct_binds_does_not_bind_registry
#print axioms validation_execution_chain
#print axioms exact_projected_fields_under_collision_exclusion
#print axioms changed_anchor_rejects_reuse_under_collision_exclusion
#print axioms projection_does_not_bind_effect_hash
#print axioms projection_does_not_bind_full_action
#print axioms execution_rechecks_authorization
#print axioms validation_execution_does_not_imply_fresh_state
#print axioms nonzero_signed_balance_is_consistent
end MacAdmission
