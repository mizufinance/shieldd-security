import ShielddSecurity.Poseidon
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.WideHashTwoBlocks960
open Poseidon
variable {F : Type} [Field F]
theorem hash (parameters : Parameters F 6) (domain : Nat)
    (inputs first second : List F) (before middle after : State F 6)
    (chunks : chunks5 inputs=[first,second])
    (initialState : before=initial domain inputs.length)
    (firstBlock : middle=permute parameters (absorb before first))
    (secondBlock : after=permute parameters (absorb middle second)) :
    after ⟨1,by decide⟩=hash6 parameters domain inputs := by
  rw [hash6,chunks,sponge]
  simp only [List.foldl_cons,List.foldl_nil,←initialState,←firstBlock,←secondBlock]
end ShielddSecurity.WideHashTwoBlocks960
set_option pp.all true in
#check @ShielddSecurity.WideHashTwoBlocks960.hash
#print axioms ShielddSecurity.WideHashTwoBlocks960.hash
