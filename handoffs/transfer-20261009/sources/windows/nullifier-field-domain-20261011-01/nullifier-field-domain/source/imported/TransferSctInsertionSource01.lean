import ShielddSecurity.TransferNoteManagerSource01

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferSctInsertionSource01

open TransferStateDelta TransferRawStateProgram01

/-! add_sct_commitment after get_sct has successfully returned a local tree.
get_sct uses expect on a fallible NV loader; that panic path is outside this
returned-result model, rather than translated into a recoverable Err. Capacity
and local insert failure precede the cache write/event. Immutable local tree
values model the required Clone/COW isolation, not proof of Rust ownership.
LocalInsert and position/commitment representations retain their SCT semantics
as named interfaces; no Merkle or durable publication result follows. -/

inductive Error (X : Type) where
  | treeFull | capacity | insert (error : X)

structure Backend (O E X Tree : Type) where
  loaded : Delta O E → Tree
  position : Tree → Option (Nat × Nat)
  localInsert : Tree → Nat → Except X (Tree × Nat)
  encode : Tree → O
  event : Nat → Nat → Bool → E

def checkCapacity {X : Type} (position : Option (Nat × Nat)) : Except (Error X) Unit :=
  match position with
  | none => .error .treeFull
  | some (_, used) => if 1 ≤ 65536 - used then .ok () else .error .capacity

def insertLoaded {O E X Tree : Type} (backend : Backend O E X Tree) (treeKey : Nat)
    (child : Delta O E) (tree : Tree) (commitment : Nat) (source : Bool) :
    TransferNoteManagerSource01.Insertion O E (Error X) :=
  match checkCapacity (X := X) (backend.position tree) with
  | .error error => ⟨child.cache, .error error⟩
  | .ok () =>
      match backend.localInsert tree commitment with
      | .error error => ⟨child.cache, .error (.insert error)⟩
      | .ok (updatedTree, position) =>
          ⟨TransferRawEffectsSource01.emit
            (putObject child treeKey (some (backend.encode updatedTree))).cache
            (backend.event commitment position source), .ok position⟩

def installSct {O E X Tree : Type}
    (manager : TransferNoteManagerSource01.Backend O E (Error X))
    (backend : Backend O E X Tree) (treeKey : Nat) : TransferNoteManagerSource01.Backend O E (Error X) :=
  {manager with sct := (fun child commitment source =>
    insertLoaded backend treeKey child (backend.loaded child) commitment source)}

theorem single_capacity_check_from_bounded_used {X : Type} (fullPosition used : Nat) (bounded : used < 65536) :
    checkCapacity (X := X) (some (fullPosition, used)) = .ok () := by
  have enough : 1 ≤ 65536 - used := by omega
  simp only [checkCapacity, if_pos enough]

theorem capacity_failure_retains_input_cache {O E X Tree : Type} (backend : Backend O E X Tree)
    (treeKey : Nat) (child : Delta O E) (tree : Tree) (commitment : Nat) (source : Bool)
    (error : Error X) (rejected : checkCapacity (backend.position tree) = .error error) :
    insertLoaded backend treeKey child tree commitment source = ⟨child.cache, .error error⟩ := by
  simp only [insertLoaded, rejected]

theorem local_insert_failure_retains_input_cache {O E X Tree : Type} (backend : Backend O E X Tree)
    (treeKey : Nat) (child : Delta O E) (tree : Tree) (commitment : Nat) (source : Bool) (error : X)
    (allowed : checkCapacity (X := X) (backend.position tree) = .ok ())
    (rejected : backend.localInsert tree commitment = .error error) :
    insertLoaded backend treeKey child tree commitment source = ⟨child.cache, .error (.insert error)⟩ := by
  simp only [insertLoaded, allowed, rejected]

theorem local_insert_success_writes_tree_then_event {O E X Tree : Type} (backend : Backend O E X Tree)
    (treeKey : Nat) (child : Delta O E) (tree updatedTree : Tree) (commitment position : Nat) (source : Bool)
    (allowed : checkCapacity (X := X) (backend.position tree) = .ok ())
    (inserted : backend.localInsert tree commitment = .ok (updatedTree, position)) :
    insertLoaded backend treeKey child tree commitment source =
      ⟨TransferRawEffectsSource01.emit (putObject child treeKey (some (backend.encode updatedTree))).cache
        (backend.event commitment position source), .ok position⟩ := by
  simp only [insertLoaded, allowed, inserted]

theorem success_derives_actual_capacity_insert_and_position {O E X Tree : Type}
    (backend : Backend O E X Tree) (treeKey : Nat) (child : Delta O E) (tree : Tree)
    (commitment position : Nat) (source : Bool) (updated : Cache O E)
    (success : insertLoaded backend treeKey child tree commitment source = ⟨updated, .ok position⟩) :
    checkCapacity (X := X) (backend.position tree) = .ok () ∧ ∃ updatedTree,
      backend.localInsert tree commitment = .ok (updatedTree, position) ∧
      updated = TransferRawEffectsSource01.emit
        (putObject child treeKey (some (backend.encode updatedTree))).cache
        (backend.event commitment position source) := by
  cases observedCapacity : checkCapacity (X := X) (backend.position tree) with
  | error error => simp [insertLoaded, observedCapacity] at success
  | ok returnedUnit =>
    cases returnedUnit
    cases observedInsert : backend.localInsert tree commitment with
    | error error => simp [insertLoaded, observedCapacity, observedInsert] at success
    | ok returned =>
      rcases returned with ⟨updatedTree, returnedPosition⟩
      have same :
          TransferRawEffectsSource01.emit
            (putObject child treeKey (some (backend.encode updatedTree))).cache
            (backend.event commitment returnedPosition source) = updated ∧ returnedPosition = position := by
        simpa [insertLoaded, observedCapacity, observedInsert] using success
      obtain ⟨cacheSame, positionSame⟩ := same
      subst returnedPosition
      exact ⟨rfl, updatedTree, rfl, cacheSame.symm⟩

theorem successful_insertion_frames_input_writes_and_other_objects {O E X Tree : Type}
    (backend : Backend O E X Tree) (treeKey : Nat) (child : Delta O E) (tree : Tree)
    (commitment position : Nat) (source : Bool) (updated : Cache O E)
    (success : insertLoaded backend treeKey child tree commitment source = ⟨updated, .ok position⟩) :
    updated.verifiable = child.cache.verifiable ∧ updated.nonverifiable = child.cache.nonverifiable ∧
      updated.events = child.cache.events ++ [backend.event commitment position source] ∧
      ∀ other, other ≠ treeKey → updated.objects other = child.cache.objects other := by
  obtain ⟨_, _, _, same⟩ := success_derives_actual_capacity_insert_and_position
    backend treeKey child tree commitment position source updated success
  rw [same]
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro other different
  simp only [TransferRawEffectsSource01.emit, putObject, if_neg different]

theorem missing_tree_position_refuses_note_callback_before_semantic_event {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (Error X))
    (manager : TransferNoteManagerSource01.Backend O E (Error X)) (backend : Backend O E X Tree)
    (treeKey pendingKey : Nat) (child : Delta O E) (output : Nat) (source : Bool) (rest : List Nat)
    (full : backend.position (backend.loaded child) = none) :
    TransferRawEffectsSource01.notes
      (TransferNoteManagerSource01.installNotes raw (installSct manager backend treeKey) pendingKey)
      source child (output :: rest) = ⟨child.cache, .error (.callback .treeFull)⟩ := by
  apply TransferNoteManagerSource01.note_callback_sct_failure_stops_semantic_event_and_suffix
  change insertLoaded backend treeKey child (backend.loaded child) output source = _
  apply capacity_failure_retains_input_cache
  simp only [checkCapacity, full]

theorem single_note_success_emits_commitment_then_note_created {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (Error X))
    (manager : TransferNoteManagerSource01.Backend O E (Error X)) (backend : Backend O E X Tree)
    (treeKey pendingKey : Nat) (child : Delta O E) (output position : Nat) (source : Bool) (updatedTree : Tree)
    (allowed : checkCapacity (X := X) (backend.position (backend.loaded child)) = .ok ())
    (inserted : backend.localInsert (backend.loaded child) output = .ok (updatedTree, position)) :
    (TransferRawEffectsSource01.notes
      (TransferNoteManagerSource01.installNotes raw (installSct manager backend treeKey) pendingKey)
      source child [output]).cache.events =
        child.cache.events ++ [backend.event output position source, raw.noteEvent output] := by
  have passed := local_insert_success_writes_tree_then_event backend treeKey child
    (backend.loaded child) updatedTree output position source allowed inserted
  have events := TransferNoteManagerSource01.note_callback_success_preserves_internal_events_then_adds_semantic_event
    raw (installSct manager backend treeKey) pendingKey child output position source _ passed
  simpa [TransferRawEffectsSource01.emit, putObject, List.append_assoc] using events

set_option pp.all true in
#check @Error
#print axioms Error
set_option pp.all true in
#check @Backend
#print axioms Backend
set_option pp.all true in
#check @checkCapacity
#print axioms checkCapacity
set_option pp.all true in
#check @insertLoaded
#print axioms insertLoaded
set_option pp.all true in
#check @installSct
#print axioms installSct
set_option pp.all true in
#check @single_capacity_check_from_bounded_used
#print axioms single_capacity_check_from_bounded_used
set_option pp.all true in
#check @capacity_failure_retains_input_cache
#print axioms capacity_failure_retains_input_cache
set_option pp.all true in
#check @local_insert_failure_retains_input_cache
#print axioms local_insert_failure_retains_input_cache
set_option pp.all true in
#check @local_insert_success_writes_tree_then_event
#print axioms local_insert_success_writes_tree_then_event
set_option pp.all true in
#check @success_derives_actual_capacity_insert_and_position
#print axioms success_derives_actual_capacity_insert_and_position
set_option pp.all true in
#check @successful_insertion_frames_input_writes_and_other_objects
#print axioms successful_insertion_frames_input_writes_and_other_objects
set_option pp.all true in
#check @missing_tree_position_refuses_note_callback_before_semantic_event
#print axioms missing_tree_position_refuses_note_callback_before_semantic_event
set_option pp.all true in
#check @single_note_success_emits_commitment_then_note_created
#print axioms single_note_success_emits_commitment_then_note_created

end ShielddSecurity.TransferSctInsertionSource01
