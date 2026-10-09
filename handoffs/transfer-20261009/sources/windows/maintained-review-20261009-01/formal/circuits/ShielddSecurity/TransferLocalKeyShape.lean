import Init.Data.List.Basic

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferLocalKeyShape

/-!
Owned matches_relation and per-family validate_relation cache model. Complete
key equality includes the remaining decoded key fields, not just digest labels.
Column lists stand for the exact sparse native public-column values and order.
Their native codec and computation are separate source obligations. The fixed
compiled relation is immutable during this execution. Setup trust, decoded
group validity and Pari security are not conclusions of structural matching.
-/

structure Key where
  relationDigest : Nat
  domain : Nat
  publicCount : Nat
  blocks : List Nat
  publicColumns : List Nat
  otherDecodedFields : List Nat
  deriving DecidableEq

structure Relation where
  digest : Nat
  domain : Nat
  publicCount : Nat
  blocks : List Nat
  computedPublicColumns : Option (List Nat)

def ShapeMatches (key : Key) (relation : Relation) : Prop :=
  key.relationDigest = relation.digest ∧ key.domain = relation.domain ∧
    key.publicCount = relation.publicCount ∧ key.blocks = relation.blocks ∧
    relation.computedPublicColumns = some key.publicColumns

instance (key : Key) (relation : Relation) : Decidable (ShapeMatches key relation) := by
  unfold ShapeMatches
  infer_instance

structure Request where
  key : Key
  manifestDomain : Nat
  deriving DecidableEq

def RequestValid (relation : Relation) (request : Request) : Prop :=
  ShapeMatches request.key relation ∧ request.manifestDomain = relation.domain

instance (relation : Relation) (request : Request) : Decidable (RequestValid relation request) := by
  unfold RequestValid
  infer_instance

def CacheValid (relation : Relation) : Option Request → Prop
  | none => True
  | some request => RequestValid relation request

def validate (relation : Relation) (cached : Option Request) (request : Request) : Option Request :=
  if cached = some request then some request
  else if RequestValid relation request then some request else none

def replay (relation : Relation) (cached : Option Request) :
    List Request → Option (Option Request)
  | [] => some cached
  | request :: rest =>
      match validate relation cached request with
      | none => none
      | some next => replay relation (some next) rest

theorem shape_success_exact (key : Key) (relation : Relation)
    (bound : ShapeMatches key relation) :
    key.relationDigest = relation.digest ∧ key.domain = relation.domain ∧
      key.publicCount = relation.publicCount ∧ key.blocks = relation.blocks ∧
      relation.computedPublicColumns = some key.publicColumns := bound

theorem digest_label_cannot_bypass_shape (key : Key) (relation : Relation)
    (wrongDomain : key.domain ≠ relation.domain) : ¬ ShapeMatches key relation := by
  intro matched
  exact wrongDomain matched.2.1

theorem computed_columns_failure_refused (key : Key) (relation : Relation)
    (failed : relation.computedPublicColumns = none) : ¬ ShapeMatches key relation := by
  intro matched
  have impossible : (none : Option (List Nat)) = some key.publicColumns :=
    failed.symm.trans matched.2.2.2.2
  cases impossible

theorem cache_hit_complete_identity (relation : Relation) (cached request : Request)
    (same : some cached = some request) :
    cached.key = request.key ∧ cached.manifestDomain = request.manifestDomain ∧
      validate relation (some cached) request = some request := by
  have identity : cached = request := Option.some.inj same
  subst cached
  exact ⟨rfl, rfl, by simp only [validate, if_true]⟩

theorem validation_preserves_cache (relation : Relation) (cached : Option Request)
    (prior : CacheValid relation cached) (request result : Request)
    (success : validate relation cached request = some result) :
    RequestValid relation result := by
  by_cases reused : cached = some request
  · have same : request = result := Option.some.inj
      (by simpa only [validate, if_pos reused] using success)
    rw [reused] at prior
    rw [← same]
    exact prior
  · by_cases valid : RequestValid relation request
    · have same : request = result := Option.some.inj
        (by simpa only [validate, if_neg reused, if_pos valid] using success)
      rw [← same]
      exact valid
    · simp only [validate, if_neg reused, if_neg valid] at success
      cases success

theorem replay_preserves_cache (relation : Relation) (requests : List Request) :
    ∀ cached result, CacheValid relation cached →
      replay relation cached requests = some result → CacheValid relation result := by
  induction requests with
  | nil =>
      intro cached result prior success
      have same : cached = result := Option.some.inj success
      rw [← same]
      exact prior
  | cons request rest ih =>
      intro cached result prior success
      cases checked : validate relation cached request with
      | none =>
          simp only [replay, checked] at success
          cases success
      | some next =>
          have valid : CacheValid relation (some next) :=
            validation_preserves_cache relation cached prior request next checked
          exact ih (some next) result valid
            (by simpa only [replay, checked] using success)

theorem empty_cache_execution_valid (relation : Relation) (requests : List Request)
    (result : Option Request) (success : replay relation none requests = some result) :
    CacheValid relation result := by
  exact replay_preserves_cache relation requests none result True.intro success

set_option pp.all true in
#check @shape_success_exact
#print axioms shape_success_exact
set_option pp.all true in
#check @digest_label_cannot_bypass_shape
#print axioms digest_label_cannot_bypass_shape
set_option pp.all true in
#check @computed_columns_failure_refused
#print axioms computed_columns_failure_refused
set_option pp.all true in
#check @cache_hit_complete_identity
#print axioms cache_hit_complete_identity
set_option pp.all true in
#check @validation_preserves_cache
#print axioms validation_preserves_cache
set_option pp.all true in
#check @replay_preserves_cache
#print axioms replay_preserves_cache
set_option pp.all true in
#check @empty_cache_execution_valid
#print axioms empty_cache_execution_valid

end ShielddSecurity.TransferLocalKeyShape
