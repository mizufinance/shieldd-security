import ShielddSecurity.PoseidonRoundSuffix05
set_option autoImplicit false
namespace ShielddSecurity.PoseidonTwoBlockComposition11
open Poseidon PoseidonRoundSuffix05
variable {F : Type} [Field F]

/-- Symbolic induction, without expanding the65 concrete round bodies. -/
theorem suffix_after_prefix (parameters : Parameters F 6) (start count : Nat) (initialState : State F 6) :
    roundsFrom parameters start count (rounds parameters start initialState)=rounds parameters (start+count) initialState := by
  induction count with
  | zero => simp only [roundsFrom,Nat.add_zero]
  | succ count ih =>
    simp only [roundsFrom,ih,Nat.add_succ,rounds]
    rfl

/-- The independent hash6 definition supplies the five-word chunking rule. -/
theorem hash6_of_two_blocks (parameters : Parameters F 6) (domain : Nat) (first second : List F)
    (before middle finalState : State F 6)
    (chunked : chunks5 (first++second)=[first,second])
    (initialState : before=initial domain (first++second).length)
    (firstResult : middle=permute parameters (absorb before first))
    (secondResult : finalState=permute parameters (absorb middle second)) :
    finalState 1=hash6 parameters domain (first++second) := by
  rw [hash6,chunked,sponge]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [←initialState,←firstResult,←secondResult]
  rfl

end ShielddSecurity.PoseidonTwoBlockComposition11
set_option pp.all true in
#check @ShielddSecurity.PoseidonTwoBlockComposition11.suffix_after_prefix
#print axioms ShielddSecurity.PoseidonTwoBlockComposition11.suffix_after_prefix
set_option pp.all true in
#check @ShielddSecurity.PoseidonTwoBlockComposition11.hash6_of_two_blocks
#print axioms ShielddSecurity.PoseidonTwoBlockComposition11.hash6_of_two_blocks
