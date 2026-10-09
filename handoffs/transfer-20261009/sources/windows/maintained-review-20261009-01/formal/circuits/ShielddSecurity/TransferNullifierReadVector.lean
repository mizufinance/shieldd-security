import Lean

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferNullifierReadVector

/-! Functional model of Reader.contains' ordered `map`/`collect<Result<Vec<bool>>>`.
`readOne` denotes the status/verify/return block at one fixed read boundary.
Authentication, boundary capture, lock ownership and Rust correspondence remain
separate obligations. An error returns no partial spentness vector. -/

def collect {E : Type} (readOne : Nat → Except E Bool) : List Nat → Except E (List Bool)
  | [] => .ok []
  | nullifier :: rest =>
      match readOne nullifier with
      | .error failure => .error failure
      | .ok spent =>
          match collect readOne rest with
          | .error failure => .error failure
          | .ok tail => .ok (spent :: tail)

def Matches {E : Type} (readOne : Nat → Except E Bool) : List Nat → List Bool → Prop
  | [], [] => True
  | nullifier :: rest, spent :: tail =>
      readOne nullifier = .ok spent ∧ Matches readOne rest tail
  | _, _ => False

theorem empty_collect {E : Type} (readOne : Nat → Except E Bool) :
    collect readOne [] = .ok [] := rfl

theorem head_error_propagates {E : Type} (readOne : Nat → Except E Bool)
    (nullifier : Nat) (rest : List Nat) (failure : E)
    (failed : readOne nullifier = .error failure) :
    collect readOne (nullifier :: rest) = .error failure := by
  simp [collect, failed]

theorem tail_error_propagates {E : Type} (readOne : Nat → Except E Bool)
    (nullifier : Nat) (rest : List Nat) (spent : Bool) (failure : E)
    (head : readOne nullifier = .ok spent)
    (failed : collect readOne rest = .error failure) :
    collect readOne (nullifier :: rest) = .error failure := by
  simp [collect, head, failed]

theorem successful_collect_matches {E : Type} (readOne : Nat → Except E Bool)
    (request : List Nat) (result : List Bool)
    (success : collect readOne request = .ok result) :
    Matches readOne request result := by
  induction request generalizing result with
  | nil =>
      have empty : result = [] := by simpa [collect] using success.symm
      subst result
      trivial
  | cons nullifier rest ih =>
      cases head : readOne nullifier with
      | error failure => simp [collect, head] at success
      | ok spent =>
          cases tail : collect readOne rest with
          | error failure => simp [collect, head, tail] at success
          | ok remaining =>
              have same : spent :: remaining = result := by
                simpa [collect, head, tail] using success
              subst result
              exact ⟨head, ih remaining tail⟩

theorem matches_has_exact_length {E : Type} (readOne : Nat → Except E Bool)
    (request : List Nat) (result : List Bool) (agreement : Matches readOne request result) :
    result.length = request.length := by
  induction request generalizing result with
  | nil =>
      cases result with
      | nil => rfl
      | cons spent rest => simp [Matches] at agreement
  | cons nullifier rest ih =>
      cases result with
      | nil => simp [Matches] at agreement
      | cons spent remaining =>
          have tail : Matches readOne rest remaining := agreement.2
          simpa only [List.length_cons] using congrArg Nat.succ (ih remaining tail)

theorem successful_collect_has_exact_length {E : Type} (readOne : Nat → Except E Bool)
    (request : List Nat) (result : List Bool)
    (success : collect readOne request = .ok result) :
    result.length = request.length :=
  matches_has_exact_length readOne request result
    (successful_collect_matches readOne request result success)

set_option pp.all true in
#check @empty_collect
#print axioms empty_collect
set_option pp.all true in
#check @head_error_propagates
#print axioms head_error_propagates
set_option pp.all true in
#check @tail_error_propagates
#print axioms tail_error_propagates
set_option pp.all true in
#check @successful_collect_matches
#print axioms successful_collect_matches
set_option pp.all true in
#check @matches_has_exact_length
#print axioms matches_has_exact_length
set_option pp.all true in
#check @successful_collect_has_exact_length
#print axioms successful_collect_has_exact_length

end ShielddSecurity.TransferNullifierReadVector
