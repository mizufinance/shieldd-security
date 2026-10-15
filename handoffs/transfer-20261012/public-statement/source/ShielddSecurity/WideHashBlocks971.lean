import ShielddSecurity.Poseidon
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.WideHashBlocks971

theorem fold_states {S A : Type} (step : S → A → S) (parts : List A)
    (states : Nat → S)
    (advance : ∀ i (inside : i<parts.length), states (i+1)=step (states i) parts[i]) :
    parts.foldl step (states 0)=states parts.length := by
  induction parts generalizing states with
  | nil => rfl
  | cons first rest ih =>
    have initialStep : states 1=step (states 0) first := advance 0 (by simp)
    rw [List.foldl_cons,←initialStep]
    apply ih (fun i => states (i+1))
    intro i inside
    exact advance (i+1) (by simpa only [List.length_cons] using Nat.succ_lt_succ inside)

open Poseidon
variable {F : Type} [Field F]
theorem hash (parameters : Parameters F 6) (domain : Nat)
    (inputs : List F) (parts : List (List F)) (states : Nat → State F 6)
    (chunks : chunks5 inputs=parts) (nonempty : parts≠[])
    (initialState : states 0=initial domain inputs.length)
    (advance : ∀ i (inside : i<parts.length),
      states (i+1)=permute parameters (absorb (states i) parts[i])) :
    states parts.length ⟨1,by decide⟩=hash6 parameters domain inputs := by
  have folded := fold_states (fun state chunk => permute parameters (absorb state chunk)) parts states advance
  cases parts with
  | nil => exact (nonempty rfl).elim
  | cons first rest =>
    rw [hash6,chunks,sponge,←initialState,folded]
end ShielddSecurity.WideHashBlocks971

set_option pp.all true in
#check @ShielddSecurity.WideHashBlocks971.fold_states
#print axioms ShielddSecurity.WideHashBlocks971.fold_states

set_option pp.all true in
#check @ShielddSecurity.WideHashBlocks971.hash
#print axioms ShielddSecurity.WideHashBlocks971.hash
