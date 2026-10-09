import ShielddSecurity.TransferOwnershipGame

set_option maxHeartbeats 300000

namespace ShielddSecurity.TransferMemoCollision

open scoped BigOperators

local instance : IsOrderedAddMonoid ℚ where
  add_le_add_left := fun _ _ inequality _ => Rat.add_le_add_right.2 inequality
local instance : IsStrictOrderedRing ℚ := .of_mul_pos fun _ _ left right ↦
  (Rat.mul_nonneg left.le right.le).lt_of_ne' (mul_ne_zero left.ne' right.ne')

/-! Raw memoized IVK query bookkeeping. Zero answers and rejected FVK calls
remain in the table. Replays contribute no fresh target charge. Probability
lemmas use the existing named universal raw-fresh primitive law, before caller
filtering; no concrete Poseidon distribution or selected acceptance law is
introduced. Applying that law requires the complete pre-answer history and
the exact source parameter family, domain, arity and ordered inputs. -/

structure SourceKey (Parameters : Type) where
  parameters : Parameters
  payload : TransferOwnershipGame.QueryKey

def familyKey {Parameters : Type} (parameters : Parameters)
    (nk : Nat) (ak : TransferCore.Affine) : SourceKey Parameters :=
  ⟨parameters,TransferOwnershipGame.ivkQuery nk ak⟩

theorem family_key_source {Parameters : Type} (parameters : Parameters)
    (nk : Nat) (ak : TransferCore.Affine) :
    (familyKey parameters nk ak).parameters = parameters ∧
      (familyKey parameters nk ak).payload.domain = 16 ∧
      (familyKey parameters nk ak).payload.arity = 3 ∧
      (familyKey parameters nk ak).payload.inputs = [nk,ak.x,ak.y] :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem family_key_injective {Parameters : Type} (parameters : Parameters)
    (leftNK rightNK : Nat) (leftAK rightAK : TransferCore.Affine)
    (same : familyKey parameters leftNK leftAK = familyKey parameters rightNK rightAK) :
    leftNK = rightNK ∧ leftAK = rightAK :=
  TransferOwnershipGame.ivk_query_injective _ _ _ _ (congrArg SourceKey.payload same)

theorem replay_no_new_alias
    (sample : TransferOwnershipGame.QueryKey → TransferReducedKeyCounting.Output)
    (key : TransferOwnershipGame.QueryKey) (table : TransferOwnershipGame.Table)
    (answer : TransferReducedKeyCounting.Output)
    (found : TransferOwnershipGame.lookup key table = some answer) :
    (TransferOwnershipGame.query sample key table).table = table ∧
      (TransferOwnershipGame.query sample key table).fresh = false := by
  simp [TransferOwnershipGame.query,found]

def targetCharge
    (sample : TransferOwnershipGame.QueryKey → TransferReducedKeyCounting.Output) :
    List TransferOwnershipGame.QueryKey → TransferOwnershipGame.Table → Nat
  | [], _ => 0
  | key :: rest, table =>
      let reply := TransferOwnershipGame.query sample key table
      (if reply.fresh then table.length else 0) + targetCharge sample rest reply.table

def triangular : Nat → Nat
  | 0 => 0
  | count+1 => triangular count + count

theorem triangular_rational (count : Nat) :
    (triangular count : ℚ) = (count : ℚ) * ((count : ℚ)-1) / 2 := by
  induction count with
  | zero => simp only [triangular,Nat.cast_zero,zero_mul,zero_div]
  | succ count ih =>
      simp only [triangular,Nat.cast_add,Nat.cast_one,ih]
      ring

theorem trace_target_charge
    (sample : TransferOwnershipGame.QueryKey → TransferReducedKeyCounting.Output)
    (keys : List TransferOwnershipGame.QueryKey) (table : TransferOwnershipGame.Table) :
    targetCharge sample keys table =
      table.length * (TransferOwnershipGame.queryTrace sample keys table).2 +
        triangular (TransferOwnershipGame.queryTrace sample keys table).2 := by
  induction keys generalizing table with
  | nil => simp [targetCharge,TransferOwnershipGame.queryTrace,triangular]
  | cons key rest ih =>
      cases found : TransferOwnershipGame.lookup key table with
      | some answer =>
          simpa only [targetCharge,TransferOwnershipGame.queryTrace,
            TransferOwnershipGame.query,found,Bool.false_eq_true,if_false,zero_add] using ih table
      | none =>
          simp only [targetCharge,TransferOwnershipGame.queryTrace,
            TransferOwnershipGame.query,found,if_true,List.length_cons]
          have step (count : Nat) : triangular (1+count) = triangular count + count := by
            rw [Nat.add_comm 1 count]
            rfl
          rw [ih,step]
          simp only [List.length_cons]
          ring

variable {Sample History : Type} [Fintype Sample] [Fintype History]
  {experiment : TransferReducedKeyQueries.FiniteExperiment Sample}

def retarget (call : TransferOwnershipGame.RawFreshQuery (History := History) experiment)
    (target : History → Nat) : TransferOwnershipGame.RawFreshQuery (History := History) experiment :=
  { call with attempt := { call.attempt with target := target } }

def priorTarget (call : TransferOwnershipGame.RawFreshQuery (History := History) experiment)
    (past : History) (index : Nat) : Nat :=
  ((call.before past).map (fun entry => TransferOwnershipGame.reduced entry.2)).getD index 0

def targetQueries (call : TransferOwnershipGame.RawFreshQuery (History := History) experiment)
    (capacity : Nat) : List (TransferOwnershipGame.RawFreshQuery (History := History) experiment) :=
  (List.finRange capacity).map (fun index => retarget call (fun past => priorTarget call past index.val))

def priorHit (call : TransferOwnershipGame.RawFreshQuery (History := History) experiment) : Sample → Bool :=
  fun sample => (call.before (call.history sample)).any
    (fun entry => decide (TransferOwnershipGame.reduced (call.answer sample) = TransferOwnershipGame.reduced entry.2))

theorem prior_hit_is_listed
    (call : TransferOwnershipGame.RawFreshQuery (History := History) experiment)
    (capacity : Nat) (sample : Sample)
    (bounded : (call.before (call.history sample)).length ≤ capacity)
    (hit : priorHit call sample = true) :
    TransferReducedKeyQueries.anyHit ((targetQueries call capacity).map TransferOwnershipGame.rawHit) sample = true := by
  obtain ⟨entry,member,accepted⟩ := List.any_eq_true.mp hit
  have included : TransferOwnershipGame.reduced entry.2 ∈
      (call.before (call.history sample)).map (fun entry => TransferOwnershipGame.reduced entry.2) :=
    List.mem_map.mpr ⟨entry,member,rfl⟩
  obtain ⟨index,selected⟩ := List.mem_iff_getElem?.mp included
  have inside := (List.getElem?_eq_some_iff.mp selected).1
  simp only [List.length_map] at inside
  let slot : Fin capacity := ⟨index,Nat.lt_of_lt_of_le inside bounded⟩
  have value : priorTarget call (call.history sample) slot.val = TransferOwnershipGame.reduced entry.2 := by
    simp only [priorTarget,slot,List.getD_eq_getElem?_getD,selected,Option.getD_some]
  let target := retarget call (fun past => priorTarget call past slot.val)
  have recorded : target ∈ targetQueries call capacity :=
    List.mem_map.mpr ⟨slot,List.mem_finRange slot,rfl⟩
  apply List.any_eq_true.mpr
  refine ⟨TransferOwnershipGame.rawHit target,List.mem_map.mpr ⟨target,recorded,rfl⟩,?_⟩
  change decide (TransferOwnershipGame.reduced (call.answer sample) =
    priorTarget call (call.history sample) slot.val) = true
  rw [value]
  exact accepted

theorem target_queries_bound
    (call : TransferOwnershipGame.RawFreshQuery (History := History) experiment)
    (capacity : Nat) :
    TransferReducedKeyQueries.eventProbability experiment
      (TransferReducedKeyQueries.anyHit ((targetQueries call capacity).map TransferOwnershipGame.rawHit)) ≤
      (capacity : ℚ) * (9 / (Scalar.modulus : ℚ)) := by
  simpa only [targetQueries,List.length_map,List.length_finRange] using
    TransferOwnershipGame.raw_fresh_union_bound (targetQueries call capacity)

/-- Raw fresh calls are indexed by their chronological fresh-query number.
The target lists include every earlier memoized answer, without a nonzero or
accepted-call filter. Connecting these indexed calls to a concrete transcript
requires complete-history and fresh/replay bookkeeping, not an event law. -/
def pairQueries (calls : Nat → TransferOwnershipGame.RawFreshQuery (History := History) experiment) :
    Nat → List (TransferOwnershipGame.RawFreshQuery (History := History) experiment)
  | 0 => []
  | count+1 => pairQueries calls count ++ targetQueries (calls count) count

theorem pair_queries_length
    (calls : Nat → TransferOwnershipGame.RawFreshQuery (History := History) experiment)
    (count : Nat) : (pairQueries calls count).length = triangular count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [pairQueries,List.length_append,ih,targetQueries,List.length_map,List.length_finRange,triangular]

theorem pair_queries_contains
    (calls : Nat → TransferOwnershipGame.RawFreshQuery (History := History) experiment)
    (count index : Nat) (inside : index < count)
    (query : TransferOwnershipGame.RawFreshQuery (History := History) experiment)
    (recorded : query ∈ targetQueries (calls index) index) :
    query ∈ pairQueries calls count := by
  induction count with
  | zero => omega
  | succ count ih =>
      by_cases last : index = count
      · subst index
        exact List.mem_append.mpr (Or.inr recorded)
      · exact List.mem_append.mpr (Or.inl (ih (by omega)))

theorem raw_pair_collision_bound
    (calls : Nat → TransferOwnershipGame.RawFreshQuery (History := History) experiment)
    (count : Nat) :
    TransferReducedKeyQueries.eventProbability experiment
      (TransferReducedKeyQueries.anyHit ((pairQueries calls count).map TransferOwnershipGame.rawHit)) ≤
      (count : ℚ) * ((count : ℚ)-1) * 9 / (2 * (Scalar.modulus : ℚ)) := by
  have bounded := TransferOwnershipGame.raw_fresh_union_bound (pairQueries calls count)
  rw [pair_queries_length,triangular_rational] at bounded
  have same : (count : ℚ) * ((count : ℚ)-1) / 2 * (9 / (Scalar.modulus : ℚ)) =
      (count : ℚ) * ((count : ℚ)-1) * 9 / (2 * (Scalar.modulus : ℚ)) := by
    rw [div_mul_div_comm]
  rw [same] at bounded
  exact bounded

private theorem sum_mono {I : Type} [DecidableEq I] (items : Finset I) (left right : I → ℚ)
    (each : ∀ item ∈ items, left item ≤ right item) :
    (∑ item ∈ items, left item) ≤ ∑ item ∈ items, right item := by
  induction items using Finset.induction_on with
  | empty => simp
  | @insert item rest absent ih =>
      rw [Finset.sum_insert absent,Finset.sum_insert absent]
      exact add_le_add (each item (Finset.mem_insert_self _ _))
        (ih (by intro previous present; exact each previous (Finset.mem_insert_of_mem present)))

private theorem probability_mono
    (left right : Sample → Bool)
    (included : ∀ sample, left sample = true → right sample = true) :
    TransferReducedKeyQueries.eventProbability experiment left ≤
      TransferReducedKeyQueries.eventProbability experiment right := by
  classical
  unfold TransferReducedKeyQueries.eventProbability
  apply sum_mono
  intro sample _
  cases hleft : left sample <;> cases hright : right sample
  · simp [hleft,hright]
  · simpa [hleft,hright] using experiment.nonnegative sample
  · have impossible : False := by
      simpa only [hright,Bool.false_eq_true] using included sample hleft
    exact False.elim impossible
  · simp [hleft,hright]

/-- The actual prior-memo collision event is covered by the pair query list.
Its size premise is chronological table bookkeeping, not a probability or
successful-Transfer consequence. The event is unconditional over all raw
answers; subsequent acceptance/rejection can only restrict this event. -/
theorem prior_memo_collision_bound
    (calls : Nat → TransferOwnershipGame.RawFreshQuery (History := History) experiment)
    (count : Nat)
    (historySize : ∀ index < count, ∀ sample,
      ((calls index).before ((calls index).history sample)).length ≤ index) :
    TransferReducedKeyQueries.eventProbability experiment
      (TransferReducedKeyQueries.anyHit ((List.range count).map (fun index => priorHit (calls index)))) ≤
      (count : ℚ) * ((count : ℚ)-1) * 9 / (2 * (Scalar.modulus : ℚ)) := by
  have covered : ∀ sample,
      TransferReducedKeyQueries.anyHit ((List.range count).map (fun index => priorHit (calls index))) sample = true →
      TransferReducedKeyQueries.anyHit ((pairQueries calls count).map TransferOwnershipGame.rawHit) sample = true := by
    intro sample hit
    obtain ⟨event,member,accepted⟩ := List.any_eq_true.mp hit
    obtain ⟨index,indexMember,same⟩ := List.mem_map.mp member
    have inside := List.mem_range.mp indexMember
    rw [← same] at accepted
    have listed := prior_hit_is_listed (calls index) index sample (historySize index inside sample) accepted
    obtain ⟨event,member,accepted⟩ := List.any_eq_true.mp listed
    obtain ⟨query,queryMember,same⟩ := List.mem_map.mp member
    exact List.any_eq_true.mpr ⟨event,List.mem_map.mpr
      ⟨query,pair_queries_contains calls count index inside query queryMember,same⟩,accepted⟩
  exact (probability_mono _ _ covered).trans (raw_pair_collision_bound calls count)

set_option pp.all true in
#check @family_key_source
#print axioms family_key_source
set_option pp.all true in
#check @family_key_injective
#print axioms family_key_injective
set_option pp.all true in
#check @replay_no_new_alias
#print axioms replay_no_new_alias
set_option pp.all true in
#check @triangular_rational
#print axioms triangular_rational
set_option pp.all true in
#check @trace_target_charge
#print axioms trace_target_charge
set_option pp.all true in
#check @prior_hit_is_listed
#print axioms prior_hit_is_listed
set_option pp.all true in
#check @target_queries_bound
#print axioms target_queries_bound
set_option pp.all true in
#check @pair_queries_length
#print axioms pair_queries_length
set_option pp.all true in
#check @pair_queries_contains
#print axioms pair_queries_contains
set_option pp.all true in
#check @raw_pair_collision_bound
#print axioms raw_pair_collision_bound
set_option pp.all true in
#check @prior_memo_collision_bound
#print axioms prior_memo_collision_bound

end ShielddSecurity.TransferMemoCollision
