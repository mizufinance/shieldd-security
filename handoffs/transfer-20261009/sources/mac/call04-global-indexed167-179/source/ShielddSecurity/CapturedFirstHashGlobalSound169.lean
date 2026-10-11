import ShielddSecurity.CapturedCall04GlobalBinding168
import ShielddSecurity.RegistryInputJoin24
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedFirstHashGlobalSound169
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem original_rows (rho : Nat → F)
    (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    Satisfies rho TransferPoseidonCall04Program01.originalRows :=
  RegistryInputJoin24.original_call rho
    (CapturedFullRelation58.verifier_links rho satisfied).2.2
    (CapturedCall04GlobalBinding168.sound rho satisfied)
theorem hash (rho : Nat → F) (one : rho 0=1)
    (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    eval rho TransferPoseidonCall04Semantic01.resultTerms =
      Poseidon.hash6 (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 23
        [rho 14,rho 15,rho 21,rho 22] :=
  TransferPoseidonCall04Semantic01.arbitrary_hash6 rho one
    CapturedRegistryLeaf20R0Proof01.four_ne_zero (original_rows rho satisfied)
theorem registry_input (rho : Nat → F) (one : rho 0=1)
    (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    eval rho (CapturedRegistryLeaf20R0Data01.inputTerms 3) =
      Poseidon.hash6 (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 23
        [rho 14,rho 15,rho 21,rho 22] := by
  rw [RegistryInputJoin24.literal_inputs.1]
  exact hash rho one satisfied
end ShielddSecurity.CapturedFirstHashGlobalSound169

set_option pp.all true in
#check @ShielddSecurity.CapturedFirstHashGlobalSound169.original_rows
#print axioms ShielddSecurity.CapturedFirstHashGlobalSound169.original_rows
set_option pp.all true in
#check @ShielddSecurity.CapturedFirstHashGlobalSound169.hash
#print axioms ShielddSecurity.CapturedFirstHashGlobalSound169.hash
set_option pp.all true in
#check @ShielddSecurity.CapturedFirstHashGlobalSound169.registry_input
#print axioms ShielddSecurity.CapturedFirstHashGlobalSound169.registry_input
