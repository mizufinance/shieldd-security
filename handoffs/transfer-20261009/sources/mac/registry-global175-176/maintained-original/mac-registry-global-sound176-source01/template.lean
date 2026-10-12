import ShielddSecurity.CapturedPriorGlobalBinding170
import ShielddSecurity.CapturedThreeCallGlobalBinding173
import ShielddSecurity.CapturedRegistryGlobalBinding175
import ShielddSecurity.RegistryInputJoin24
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryGlobalSound176
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem row_families (rho : Nat → F)
    (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    Satisfies rho CapturedPriorRows16Frame01.capturedPriorRows ∧
    Satisfies rho TransferPoseidonThreeCallJoin15Program01.originalRows ∧
    Satisfies rho RegistryWhole23.selectedRows :=
  ⟨CapturedPriorGlobalBinding170.sound rho satisfied,
    CapturedThreeCallGlobalBinding173.sound rho satisfied,
    CapturedRegistryGlobalBinding175.sound rho satisfied⟩
theorem hash (rho : Nat → F) (one : rho 0=1)
    (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    eval rho RegistryWhole23.actualResult=Poseidon.hash6
      (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 25
      (RegistryInputJoin24.semanticInputs rho) :=
  RegistryInputJoin24.arbitrary_registry rho one
    (row_families rho satisfied).1 (row_families rho satisfied).2.1 (row_families rho satisfied).2.2
end ShielddSecurity.CapturedRegistryGlobalSound176
