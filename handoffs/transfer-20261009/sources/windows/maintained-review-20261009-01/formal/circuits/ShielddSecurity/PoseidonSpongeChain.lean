import ShielddSecurity.Poseidon

set_option maxHeartbeats 400000

namespace ShielddSecurity.PoseidonSpongeChain

/-- A symbolic recurrence composes any number of certified blocks. -/
theorem fold_chain {A B : Type} (step : A → B → A) (states : Nat → A)
    (chunks : List B)
    (transition : ∀ index value, chunks[index]? = some value →
      states (index + 1) = step (states index) value) :
    states chunks.length = chunks.foldl step (states 0) := by
  induction chunks generalizing states with
  | nil => rfl
  | cons head tail ih =>
    have first : states 1 = step (states 0) head := transition 0 head rfl
    have rest : ∀ index value, tail[index]? = some value →
        states ((index + 1) + 1) = step (states (index + 1)) value := by
      intro index value member
      exact transition (index + 1) value (by simpa only [List.getElem?_cons_succ] using member)
    have result := ih (fun index => states (index + 1)) rest
    change states (tail.length + 1) = tail.foldl step (states 1) at result
    rw [first] at result
    simpa only [List.length_cons, List.foldl_cons] using result

theorem hash6_of_chain {F : Type} [Field F] (parameters : Poseidon.Parameters F 6)
    (domain : Nat) (inputs : List F) (states : Nat → Poseidon.State F 6)
    (nonempty : Poseidon.chunks5 inputs ≠ [])
    (initialState : states 0 = Poseidon.initial domain inputs.length)
    (transition : ∀ index value, (Poseidon.chunks5 inputs)[index]? = some value →
      states (index + 1) = Poseidon.permute parameters (Poseidon.absorb (states index) value)) :
    states (Poseidon.chunks5 inputs).length ⟨1, by decide⟩ =
      Poseidon.hash6 parameters domain inputs := by
  have result := fold_chain
    (fun state chunk => Poseidon.permute parameters (Poseidon.absorb state chunk))
    states (Poseidon.chunks5 inputs) transition
  rw [initialState] at result
  cases chunks : Poseidon.chunks5 inputs with
  | nil => exact False.elim (nonempty chunks)
  | cons head tail =>
    rw [chunks] at result
    simpa only [Poseidon.hash6, chunks, Poseidon.sponge] using
      congrArg (fun state : Poseidon.State F 6 => state ⟨1, by decide⟩) result

set_option pp.all true in
#check @fold_chain
#print axioms fold_chain
set_option pp.all true in
#check @hash6_of_chain
#print axioms hash6_of_chain

end ShielddSecurity.PoseidonSpongeChain
