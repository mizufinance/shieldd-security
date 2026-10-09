import ShielddSecurity.TransferProjection

set_option maxHeartbeats 150000

namespace ShielddSecurity.TransferMixedBody

/-! Exact Transfer occurrence selection from an unbounded mixed body. B retains
the complete decoded native action source; kind is its independently supplied
enum view, whose native codec/source correspondence remains to be established.
Filtering never renumbers body slots. Fee funding uses the full mixed body
length, and both spend slots plus ordinary volume contribute to the guard.
Other-family semantics and their balance openings are separate contracts. -/

inductive Kind where
  | transfer | reshape | withdrawal | registerAsset | registerUser
  deriving DecidableEq

structure Action (B : Type) where
  kind : Kind
  source : B

def bodyFrom {B : Type} (start : Nat) : List (Action B) → List (Nat × Action B)
  | [] => []
  | action :: rest => (start, action) :: bodyFrom (start + 1) rest

def selected {B : Type} (start : Nat) (body : List (Action B)) : List (Nat × Action B) :=
  (bodyFrom start body).filter fun entry => decide (entry.2.kind = .transfer)

def funding {B : Type} (body : List (Action B)) (fee : Option B) : List (Nat × Action B) :=
  fee.toList.map fun source => (body.length, ⟨.transfer, source⟩)

def complete {B : Type} (body : List (Action B)) (fee : Option B) : List (Nat × Action B) :=
  selected 0 body ++ funding body fee

theorem body_length {B : Type} (start : Nat) (body : List (Action B)) :
    (bodyFrom start body).length = body.length := by
  induction body generalizing start with
  | nil => rfl
  | cons action rest ih => simp only [bodyFrom, List.length_cons, ih]

theorem body_original_index {B : Type} (start : Nat) (body : List (Action B))
    (entry : Nat × Action B) (inside : entry ∈ bodyFrom start body) :
    start ≤ entry.1 ∧ entry.1 < start + body.length := by
  induction body generalizing start with
  | nil => simp only [bodyFrom, List.not_mem_nil] at inside
  | cons action rest ih =>
      rcases List.mem_cons.mp inside with same | tail
      · subst entry
        simp only [Prod.fst, List.length_cons]
        omega
      · have bounded := ih (start + 1) tail
        simp only [List.length_cons]
        omega

theorem selected_transfer_kind {B : Type} (start : Nat) (body : List (Action B))
    (entry : Nat × Action B) (inside : entry ∈ selected start body) :
    entry.2.kind = .transfer := by
  exact of_decide_eq_true (List.mem_filter.mp inside).2

theorem selected_original_index {B : Type} (start : Nat) (body : List (Action B))
    (entry : Nat × Action B) (inside : entry ∈ selected start body) :
    start ≤ entry.1 ∧ entry.1 < start + body.length := by
  exact body_original_index start body entry (List.mem_filter.mp inside).1

theorem selection_count {B : Type} (start : Nat) (body : List (Action B)) :
    (selected start body).length ≤ body.length := by
  have filtered := List.length_filter_le
    (fun entry : Nat × Action B => decide (entry.2.kind = .transfer)) (bodyFrom start body)
  simpa only [selected, body_length] using filtered

theorem funding_after_full_body {B : Type} (body : List (Action B)) (fee : B) :
    complete body (some fee) = selected 0 body ++ [(body.length, ⟨.transfer, fee⟩)] := by
  rfl

theorem funding_different_from_body_slot {B : Type} (body : List (Action B))
    (entry : Nat × Action B) (inside : entry ∈ selected 0 body) : entry.1 ≠ body.length := by
  have bounded := (selected_original_index 0 body entry inside).2
  omega

theorem selected_index_u32 {B : Type} (body : List (Action B))
    (entry : Nat × Action B) (inside : entry ∈ selected 0 body)
    (bounded : body.length ≤ 512) : entry.1 < 2 ^ 32 := by
  have index := (selected_original_index 0 body entry inside).2
  have capacity : 512 < 2 ^ 32 := by decide
  omega

theorem complete_selected_count {B : Type} (body : List (Action B)) (fee : Option B)
    (guard : body.length + fee.toList.length ≤ 512) : (complete body fee).length ≤ 512 := by
  have bounded := Nat.add_le_add_right (selection_count 0 body) fee.toList.length
  simpa only [complete, funding, List.length_append, List.length_map] using
    Nat.le_trans bounded guard

theorem transfer_nullifier_guard (ordinary fundingCount other : Nat)
    (guard : 3 * ordinary + 2 * fundingCount + other ≤ 256) : ordinary ≤ 85 := by
  omega

theorem funded_transfer_nullifier_guard (ordinary other : Nat)
    (guard : 3 * ordinary + 2 + other ≤ 256) : ordinary ≤ 84 := by
  omega

set_option pp.all true in
#check @body_length
#print axioms body_length
set_option pp.all true in
#check @body_original_index
#print axioms body_original_index
set_option pp.all true in
#check @selected_transfer_kind
#print axioms selected_transfer_kind
set_option pp.all true in
#check @selected_original_index
#print axioms selected_original_index
set_option pp.all true in
#check @selection_count
#print axioms selection_count
set_option pp.all true in
#check @funding_after_full_body
#print axioms funding_after_full_body
set_option pp.all true in
#check @funding_different_from_body_slot
#print axioms funding_different_from_body_slot
set_option pp.all true in
#check @selected_index_u32
#print axioms selected_index_u32
set_option pp.all true in
#check @complete_selected_count
#print axioms complete_selected_count
set_option pp.all true in
#check @transfer_nullifier_guard
#print axioms transfer_nullifier_guard
set_option pp.all true in
#check @funded_transfer_nullifier_guard
#print axioms funded_transfer_nullifier_guard

end ShielddSecurity.TransferMixedBody
