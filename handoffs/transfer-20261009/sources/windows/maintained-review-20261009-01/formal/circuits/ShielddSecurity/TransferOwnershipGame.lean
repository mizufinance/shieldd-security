import ShielddSecurity.TransferNativeSourceCatalogue
import ShielddSecurity.TransferReducedKeyQueries

set_option maxHeartbeats 250000

namespace ShielddSecurity.TransferOwnershipGame

open TransferSem TransferReducedKeyCounting
open scoped BigOperators

local instance : IsOrderedAddMonoid ℚ where
  add_le_add_left := fun _ _ inequality _ => Rat.add_le_add_right.2 inequality

local instance : IsStrictOrderedRing ℚ := .of_mul_pos fun _ _ positiveLeft positiveRight ↦
  (Rat.mul_nonneg positiveLeft.le positiveRight.le).lt_of_ne'
    (mul_ne_zero positiveLeft.ne' positiveRight.ne')

/-! Exact IVK preimages and memoized raw field answers. Zero answers are retained:
the pinned FVK constructor rejects zero reduction, rather than resampling inside
from_components. No distribution or security property of concrete Poseidon is
asserted. The signature event uses the complete source catalogue and an explicit
signing-query log; verifier success alone does not establish ownership. -/

structure QueryKey where
  domain : Nat
  arity : Nat
  inputs : List Nat
  deriving DecidableEq

def ivkQuery (nk : Nat) (ak : TransferCore.Affine) : QueryKey :=
  ⟨16, 3, [nk, ak.x, ak.y]⟩

def spongeIV (key : QueryKey) : Nat := 256 * key.arity + key.domain

theorem ivk_sponge_iv (nk : Nat) (ak : TransferCore.Affine) :
    spongeIV (ivkQuery nk ak) = 784 := by rfl

theorem ivk_query_source (nk : Nat) (ak : TransferCore.Affine) :
    (ivkQuery nk ak).domain = domainCode .incomingViewingKey ∧
      (ivkQuery nk ak).arity = (ivkQuery nk ak).inputs.length ∧
      (ivkQuery nk ak).inputs = [nk] ++ pointFields ak := by
  exact ⟨rfl, rfl, rfl⟩

theorem ivk_query_injective (leftNK rightNK : Nat) (leftAK rightAK : TransferCore.Affine)
    (same : ivkQuery leftNK leftAK = ivkQuery rightNK rightAK) :
    leftNK = rightNK ∧ leftAK = rightAK := by
  have fields := congrArg QueryKey.inputs same
  change [leftNK, leftAK.x, leftAK.y] = [rightNK, rightAK.x, rightAK.y] at fields
  have parts := List.cons.inj fields
  have coordinates := List.cons.inj parts.2
  have ys := (List.cons.inj coordinates.2).1
  exact ⟨parts.1, by cases leftAK; cases rightAK; simp_all⟩

abbrev Table := List (QueryKey × TransferReducedKeyCounting.Output)

def lookup (key : QueryKey) : Table → Option TransferReducedKeyCounting.Output
  | [] => none
  | entry :: rest => if entry.1 = key then some entry.2 else lookup key rest

theorem lookup_member (key : QueryKey) (table : Table) (answer : TransferReducedKeyCounting.Output)
    (found : lookup key table = some answer) : (key, answer) ∈ table := by
  induction table with
  | nil => cases found
  | cons entry rest ih =>
      by_cases same : entry.1 = key
      · have values : entry.2 = answer := Option.some.inj (by
          simpa only [lookup, if_pos same] using found)
        have pair : (key, answer) = entry := Prod.ext same.symm values.symm
        rw [pair]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem entry (ih (by
          simpa only [lookup, if_neg same] using found))

structure Reply where
  answer : TransferReducedKeyCounting.Output
  table : Table
  fresh : Bool

def query (sample : QueryKey → TransferReducedKeyCounting.Output) (key : QueryKey) (table : Table) : Reply :=
  match lookup key table with
  | some answer => ⟨answer, table, false⟩
  | none => ⟨sample key, (key, sample key) :: table, true⟩

theorem repeated_query (sample : QueryKey → TransferReducedKeyCounting.Output) (key : QueryKey) (table : Table)
    (answer : TransferReducedKeyCounting.Output) (found : lookup key table = some answer) :
    query sample key table = ⟨answer, table, false⟩ := by
  simp only [query, found]

theorem fresh_query (sample : QueryKey → TransferReducedKeyCounting.Output) (key : QueryKey) (table : Table)
    (absent : lookup key table = none) :
    query sample key table = ⟨sample key, (key, sample key) :: table, true⟩ := by
  simp only [query, absent]

theorem query_records_answer (sample : QueryKey → TransferReducedKeyCounting.Output) (key : QueryKey) (table : Table) :
    (key, (query sample key table).answer) ∈ (query sample key table).table := by
  cases found : lookup key table with
  | none => simp only [query, found]; exact List.mem_cons_self
  | some answer =>
      simpa only [query, found] using lookup_member key table answer found

theorem query_growth (sample : QueryKey → TransferReducedKeyCounting.Output) (key : QueryKey) (table : Table) :
    (query sample key table).table.length = table.length +
      (if (query sample key table).fresh then 1 else 0) := by
  cases found : lookup key table <;> simp [query, found]

theorem immediate_replay (sample : QueryKey → TransferReducedKeyCounting.Output) (key : QueryKey) (table : Table) :
    (query sample key (query sample key table).table).fresh = false ∧
      (query sample key (query sample key table).table).answer = (query sample key table).answer := by
  cases found : lookup key table with
  | none => simp [query, lookup, found]
  | some answer => simp [query, found]

theorem query_preserves_lookup (sample : QueryKey → TransferReducedKeyCounting.Output) (queried old : QueryKey)
    (table : Table) (answer : TransferReducedKeyCounting.Output) (found : lookup old table = some answer) :
    lookup old (query sample queried table).table = some answer := by
  cases current : lookup queried table with
  | some value => simpa only [query, current] using found
  | none =>
      have different : queried ≠ old := by
        intro same
        subst queried
        rw [found] at current
        cases current
      simpa only [query, current, lookup, if_neg different] using found

def queryTrace (sample : QueryKey → TransferReducedKeyCounting.Output) : List QueryKey → Table → Table × Nat
  | [], table => (table, 0)
  | key :: rest, table =>
      let reply := query sample key table
      let continuation := queryTrace sample rest reply.table
      (continuation.1, (if reply.fresh then 1 else 0) + continuation.2)

theorem trace_preserves_lookup (sample : QueryKey → TransferReducedKeyCounting.Output) (keys : List QueryKey)
    (table : Table) (key : QueryKey) (answer : TransferReducedKeyCounting.Output)
    (found : lookup key table = some answer) :
    lookup key (queryTrace sample keys table).1 = some answer := by
  induction keys generalizing table with
  | nil => exact found
  | cons queried rest ih =>
      exact ih _ (query_preserves_lookup sample queried key table answer found)

theorem trace_fresh_count (sample : QueryKey → TransferReducedKeyCounting.Output) (keys : List QueryKey) (table : Table) :
    (queryTrace sample keys table).1.length = table.length + (queryTrace sample keys table).2 := by
  induction keys generalizing table with
  | nil => simp only [queryTrace, Nat.add_zero]
  | cons key rest ih =>
      change (queryTrace sample rest (query sample key table).table).1.length =
        table.length + ((if (query sample key table).fresh then 1 else 0) +
          (queryTrace sample rest (query sample key table).table).2)
      rw [ih, query_growth, Nat.add_assoc]

def rawAnswerFraction (predicate : TransferReducedKeyCounting.Output → Bool) : ℚ :=
  (Fintype.card {answer : TransferReducedKeyCounting.Output // predicate answer = true} : ℚ) /
    (Fintype.card TransferReducedKeyCounting.Output : ℚ)

private def rawHitEquiv (target : Nat) :
    {answer : TransferReducedKeyCounting.Output // decide (answer.val % Scalar.order = target) = true} ≃ Fiber target where
  toFun answer := ⟨answer.val, of_decide_eq_true answer.property⟩
  invFun answer := ⟨answer.val, by simpa only [decide_eq_true_eq] using answer.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem raw_answer_fraction (target : Nat) :
    rawAnswerFraction (fun answer => decide (answer.val % Scalar.order = target)) =
      uniformHitFraction target := by
  unfold rawAnswerFraction uniformHitFraction
  rw [Fintype.card_congr (rawHitEquiv target)]
  simp only [Fintype.card_fin]

/-- A universal ideal raw-answer primitive law over every pre-answer predicate.
The typed source key is absent from the recorded pre-answer table, and the
target is a function of that history. Actual Poseidon, caller rejection or a
selected successful event cannot instantiate this record without the complete
oracle-game interpretation. All zero answers and rejected calls remain counted.
The history must include every relevant earlier/programmed oracle query. -/
structure RawFreshQuery {Sample History : Type} [Fintype Sample] [Fintype History]
    (experiment : TransferReducedKeyQueries.FiniteExperiment Sample) where
  attempt : TransferReducedKeyQueries.Attempt History
  history : Sample → History
  key : History → QueryKey
  before : History → Table
  answer : Sample → TransferReducedKeyCounting.Output
  absent : ∀ sample, lookup (key (history sample)) (before (history sample)) = none
  uniformLaw : ∀ predicate : History → TransferReducedKeyCounting.Output → Bool,
    TransferReducedKeyQueries.eventProbability experiment
      (fun sample => predicate (history sample) (answer sample)) =
      ∑ past, attempt.historyWeight past * rawAnswerFraction (predicate past)

variable {Sample History : Type} [Fintype Sample] [Fintype History]
    {experiment : TransferReducedKeyQueries.FiniteExperiment Sample}

def rawHit (call : RawFreshQuery (History := History) experiment) : Sample → Bool :=
  fun sample => decide ((call.answer sample).val % Scalar.order =
    call.attempt.target (call.history sample))

def rawReply (call : RawFreshQuery (History := History) experiment) (sample : Sample) : Reply :=
  query (fun _ => call.answer sample) (call.key (call.history sample))
    (call.before (call.history sample))

theorem raw_reply_source (call : RawFreshQuery (History := History) experiment) (sample : Sample) :
    rawReply call sample = ⟨call.answer sample,
      (call.key (call.history sample), call.answer sample) :: call.before (call.history sample), true⟩ :=
  fresh_query _ _ _ (call.absent sample)

private theorem rational_sum_mono {I : Type} [DecidableEq I] (items : Finset I)
    (left right : I → ℚ) (each : ∀ item ∈ items, left item ≤ right item) :
    (∑ item ∈ items, left item) ≤ ∑ item ∈ items, right item := by
  induction items using Finset.induction_on with
  | empty => simp
  | @insert item rest absent ih =>
      rw [Finset.sum_insert absent, Finset.sum_insert absent]
      exact add_le_add (each item (Finset.mem_insert_self _ _))
        (ih (by intro previous member; exact each previous (Finset.mem_insert_of_mem member)))

private theorem rational_sum_times {I : Type} [DecidableEq I] (items : Finset I)
    (term : I → ℚ) (coefficient : ℚ) :
    (∑ item ∈ items, term item * coefficient) = (∑ item ∈ items, term item) * coefficient := by
  induction items using Finset.induction_on with
  | empty => simp
  | @insert item rest absent ih => simp only [Finset.sum_insert absent, ih, add_mul]

theorem raw_fresh_hit_bound (call : RawFreshQuery (History := History) experiment) :
    TransferReducedKeyQueries.eventProbability experiment (rawHit call) ≤
      9 / (Scalar.modulus : ℚ) := by
  classical
  have uniform := call.uniformLaw (fun past answer =>
    decide (answer.val % Scalar.order = call.attempt.target past))
  simp only [raw_answer_fraction] at uniform
  change TransferReducedKeyQueries.eventProbability experiment
    (fun sample => decide ((call.answer sample).val % Scalar.order =
      call.attempt.target (call.history sample))) ≤ _
  rw [uniform]
  calc
    _ ≤ ∑ past, call.attempt.historyWeight past * (9 / (Scalar.modulus : ℚ)) :=
      rational_sum_mono _ _ _ (fun past _ => mul_le_mul_of_nonneg_left
        (uniform_hit_bound (call.attempt.target past)) (call.attempt.nonnegative past))
    _ = _ := by rw [rational_sum_times, call.attempt.total, one_mul]

theorem raw_fresh_union_bound (calls : List (RawFreshQuery (History := History) experiment)) :
    TransferReducedKeyQueries.eventProbability experiment
      (TransferReducedKeyQueries.anyHit (calls.map rawHit)) ≤
      (calls.length : ℚ) * (9 / (Scalar.modulus : ℚ)) := by
  have summed : ((calls.map rawHit).map
      (TransferReducedKeyQueries.eventProbability experiment)).sum ≤
      (calls.length : ℚ) * (9 / (Scalar.modulus : ℚ)) := by
    induction calls with
    | nil => simp
    | cons call rest ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        calc
          _ ≤ 9 / (Scalar.modulus : ℚ) + (rest.length : ℚ) * (9 / (Scalar.modulus : ℚ)) :=
            add_le_add (raw_fresh_hit_bound call) ih
          _ = _ := by ring
  exact (TransferReducedKeyQueries.finite_query_union_bound experiment (calls.map rawHit)).trans summed

def reduced (answer : TransferReducedKeyCounting.Output) : Nat := answer.val % Scalar.order

def admittedAnswer (answer : TransferReducedKeyCounting.Output) : Option Nat :=
  if reduced answer = 0 then none else some (reduced answer)

theorem admitted_answer_exact (answer : TransferReducedKeyCounting.Output) (scalar : Nat)
    (accepted : admittedAnswer answer = some scalar) :
    scalar = reduced answer ∧ scalar ≠ 0 ∧ scalar < Scalar.order := by
  by_cases zero : reduced answer = 0
  · simp only [admittedAnswer, if_pos zero] at accepted
    cases accepted
  · have same : reduced answer = scalar := Option.some.inj (by
      simpa only [admittedAnswer, if_neg zero] using accepted)
    refine ⟨same.symm, ?_, ?_⟩
    · rw [← same]; exact zero
    · rw [← same]; exact Nat.mod_lt _ (by decide : 0 < Scalar.order)

/-- Named global prime-subgroup law, universally quantified over canonical
scalars and independently valid nonidentity bases. This is a functional group
law, not an ownership event or a per-input collision/security premise. Its
instantiation uses the named standard curve/order contracts. -/
def FaithfulSubgroupAction (crypto : Crypto) : Prop :=
  ∀ base, ValidPoint crypto base → nonidentity base →
    ∀ left right, left < Scalar.order → right < Scalar.order →
      crypto.mul left base = crypto.mul right base → left = right

theorem scalar_reduction_from_sem (crypto : Crypto) (witness : Witness)
    (legal : AuthorizationScalarSem crypto witness) :
    crypto.hash .incomingViewingKey ([witness.auth.nk] ++ pointFields witness.auth.ak) %
      Scalar.order = witness.auth.ivk := by
  rw [legal.2.2.2]
  change (witness.auth.ivk + Scalar.order * witness.auth.quotient) % Scalar.order =
    witness.auth.ivk
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod,
    Nat.add_zero, Nat.mod_mod]
  have bound := legal.1
  change witness.auth.ivk < Scalar.order at bound
  exact Nat.mod_eq_of_lt bound

def authorizationAnswer (crypto : Crypto) (canonical : CanonicalCrypto crypto)
    (witness : Witness) : TransferReducedKeyCounting.Output :=
  ⟨crypto.hash .incomingViewingKey ([witness.auth.nk] ++ pointFields witness.auth.ak),
    canonical.1 _ _⟩

theorem extracted_authorization_answer (crypto : Crypto) (canonical : CanonicalCrypto crypto)
    (witness : Witness) (legal : AuthorizationScalarSem crypto witness) :
    (ivkQuery witness.auth.nk witness.auth.ak).inputs =
      [witness.auth.nk] ++ pointFields witness.auth.ak ∧
    admittedAnswer (authorizationAnswer crypto canonical witness) = some witness.auth.ivk := by
  have reduction : reduced (authorizationAnswer crypto canonical witness) = witness.auth.ivk := by
    change crypto.hash .incomingViewingKey ([witness.auth.nk] ++ pointFields witness.auth.ak) %
      Scalar.order = witness.auth.ivk
    exact scalar_reduction_from_sem crypto witness legal
  exact ⟨rfl, by simp only [admittedAnswer, reduction, if_neg legal.2.1]⟩

/-- Two independently established local authorization relations for the same
nonidentity diversified base/transmission force equal reduced scalars. Different
typed source keys then give a reduced-hash alias. Actual arbitrary-row semantics
must establish each AuthorizationScalarSem and multiplication equation before
applying this theorem; knowledge extraction alone does not supply them. -/
theorem same_address_reduced_alias (crypto : Crypto) (faithful : FaithfulSubgroupAction crypto)
    (left right : Witness)
    (leftScalar : AuthorizationScalarSem crypto left)
    (rightScalar : AuthorizationScalarSem crypto right)
    (validBase : ValidPoint crypto left.sender.address.diversified)
    (nonzeroBase : nonidentity left.sender.address.diversified)
    (base : right.sender.address.diversified = left.sender.address.diversified)
    (transmission : right.sender.address.transmission = left.sender.address.transmission)
    (leftOwnership : crypto.mul left.auth.ivk left.sender.address.diversified =
      left.sender.address.transmission)
    (rightOwnership : crypto.mul right.auth.ivk right.sender.address.diversified =
      right.sender.address.transmission) :
    left.auth.ivk = right.auth.ivk ∧
      crypto.hash .incomingViewingKey ([left.auth.nk] ++ pointFields left.auth.ak) % Scalar.order =
        crypto.hash .incomingViewingKey ([right.auth.nk] ++ pointFields right.auth.ak) % Scalar.order := by
  have multiplication : crypto.mul left.auth.ivk left.sender.address.diversified =
      crypto.mul right.auth.ivk left.sender.address.diversified := by
    calc
      _ = left.sender.address.transmission := leftOwnership
      _ = right.sender.address.transmission := transmission.symm
      _ = crypto.mul right.auth.ivk right.sender.address.diversified := rightOwnership.symm
      _ = _ := by rw [base]
  have same := faithful _ validBase nonzeroBase _ _ leftScalar.1 rightScalar.1 multiplication
  exact ⟨same, (scalar_reduction_from_sem crypto left leftScalar).trans
    (same.trans (scalar_reduction_from_sem crypto right rightScalar).symm)⟩

structure SignedMessage where
  key : Nat
  message : Nat
  deriving DecidableEq

def Forgery (verify : Nat → Nat → List Nat → Bool) (signingLog : List SignedMessage)
    (key message : Nat) (signature : List Nat) : Prop :=
  key ≠ 0 ∧ verify key message signature = true ∧ ⟨key, message⟩ ∉ signingLog

/-- This constructs an exact accepted signature/new-message event, not its
probability bound. Randomized AK/RK linkage, permitted key registration,
corruption queries and signing-oracle simulation remain reduction obligations.
The log records every permitted signing query even if the signer fails. -/
theorem catalogue_unsigned_message_event
    (base : TransferFullCarrierAcceptance.Model
      (TransferNativeCarrierBridge.NativeTransaction TransferNativeSourceCatalogue.Body)
      TransferNativeCarrierBridge.ActionView)
    (decode : List Nat → Option
      (TransferNativeCarrierBridge.NativeTransaction TransferNativeSourceCatalogue.Body))
    (crypto : Crypto) (input : TransferFullCarrierAcceptance.Inputs) (raw : List Nat)
    (cached : TransferWarmCache.Cached
      (TransferNativeCarrierBridge.NativeTransaction TransferNativeSourceCatalogue.Body))
    (made : TransferWarmCache.construct
      (TransferNativeCarrierBridge.contextModel (TransferNativeSourceCatalogue.catalogueModel base) decode)
      crypto (TransferNativeCarrierBridge.transferInputs input) raw = some cached)
    (entry : Nat × TransferNativeSourceCatalogue.TransferSource)
    (inside : entry ∈ TransferNativeSourceCatalogue.occurrences cached.prepared.carrier.body.body)
    (signingLog : List SignedMessage)
    (unsigned : ⟨entry.2.key,
      base.effectHash (base.effectFields cached.prepared.carrier.body)⟩ ∉ signingLog) :
    Forgery input.verifySpend signingLog entry.2.key
      (base.effectHash (base.effectFields cached.prepared.carrier.body)) entry.2.signature := by
  have checked := TransferNativeSourceCatalogue.constructed_occurrence_signature_arguments
    base decode crypto input raw cached made entry inside
  exact ⟨checked.2.1, checked.2.2, unsigned⟩

set_option pp.all true in
#check @ivk_sponge_iv
#print axioms ivk_sponge_iv
set_option pp.all true in
#check @ivk_query_source
#print axioms ivk_query_source
set_option pp.all true in
#check @ivk_query_injective
#print axioms ivk_query_injective
set_option pp.all true in
#check @lookup_member
#print axioms lookup_member
set_option pp.all true in
#check @repeated_query
#print axioms repeated_query
set_option pp.all true in
#check @fresh_query
#print axioms fresh_query
set_option pp.all true in
#check @query_records_answer
#print axioms query_records_answer
set_option pp.all true in
#check @query_growth
#print axioms query_growth
set_option pp.all true in
#check @immediate_replay
#print axioms immediate_replay
set_option pp.all true in
#check @query_preserves_lookup
#print axioms query_preserves_lookup
set_option pp.all true in
#check @trace_preserves_lookup
#print axioms trace_preserves_lookup
set_option pp.all true in
#check @trace_fresh_count
#print axioms trace_fresh_count
set_option pp.all true in
#check @raw_answer_fraction
#print axioms raw_answer_fraction
set_option pp.all true in
#check @raw_reply_source
#print axioms raw_reply_source
set_option pp.all true in
#check @raw_fresh_hit_bound
#print axioms raw_fresh_hit_bound
set_option pp.all true in
#check @raw_fresh_union_bound
#print axioms raw_fresh_union_bound
set_option pp.all true in
#check @admitted_answer_exact
#print axioms admitted_answer_exact
set_option pp.all true in
#check @scalar_reduction_from_sem
#print axioms scalar_reduction_from_sem
set_option pp.all true in
#check @extracted_authorization_answer
#print axioms extracted_authorization_answer
set_option pp.all true in
#check @same_address_reduced_alias
#print axioms same_address_reduced_alias
set_option pp.all true in
#check @catalogue_unsigned_message_event
#print axioms catalogue_unsigned_message_event

end ShielddSecurity.TransferOwnershipGame
