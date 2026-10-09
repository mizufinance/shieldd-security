import ShielddSecurity.PoseidonRoundSuffix09
namespace ShielddSecurity.PoseidonSuffixComposition10
open Poseidon PoseidonRoundSuffix09
variable {F : Type} [Field F] {width : Nat}
/-- Symbolic prefix/suffix composition; no literal 65-round reduction. -/
theorem suffix_after_prefix (parameters : Parameters F width) (start count : Nat) (initial : State F width) :
    roundsFrom parameters start count (rounds parameters start initial)=rounds parameters (start+count) initial := by
  induction count with
  | zero => simp only [roundsFrom,Nat.add_zero]
  | succ count ih => simp only [roundsFrom,ih,Nat.add_succ,rounds]
end ShielddSecurity.PoseidonSuffixComposition10
set_option pp.all true in
#check @ShielddSecurity.PoseidonSuffixComposition10.suffix_after_prefix
#print axioms ShielddSecurity.PoseidonSuffixComposition10.suffix_after_prefix
