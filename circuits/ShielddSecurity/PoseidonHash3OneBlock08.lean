import ShielddSecurity.Poseidon
namespace ShielddSecurity.PoseidonHash3OneBlock08
open Poseidon
variable {F : Type} [Field F]
/-- Join an exact one-chunk permutation to the independent narrow sponge. -/
theorem hash3_of_one_block (parameters : Parameters F 3) (domain : Nat)
    (inputs : List F) (before after : State F 3)
    (chunks : chunks2 inputs=[inputs])
    (initialState : before=initial domain inputs.length)
    (block : after=permute parameters (absorb before inputs)) :
    after ⟨1,by decide⟩=hash3 parameters domain inputs := by
  rw [hash3,chunks,sponge]
  simpa only [List.foldl_cons,List.foldl_nil,← initialState] using
    congrArg (fun state : State F 3 => state ⟨1,by decide⟩) block
set_option pp.all true in
#check @ShielddSecurity.PoseidonHash3OneBlock08.hash3_of_one_block
#print axioms ShielddSecurity.PoseidonHash3OneBlock08.hash3_of_one_block
end ShielddSecurity.PoseidonHash3OneBlock08
