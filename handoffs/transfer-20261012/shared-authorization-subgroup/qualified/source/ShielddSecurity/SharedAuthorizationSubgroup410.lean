import ShielddSecurity.AuthorizationPointConstruction408
import ShielddSecurity.AuthorizationSubgroupCapture409B05
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedAuthorizationSubgroup410
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

theorem input_roles (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (binding : CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) authInitial=SubgroupSeedCompletion203.fieldPoint w.auth.ak) :
    CapturedFourSubgroupConstructor88.InputRoles
      (fun column => SemanticWordFrame373.assignment (AuthorizationPointSeed405.seed original w authInitial) c w initial senderInitial receiverInitial
        (AuthorizationSubgroupCapture409B05.rename column)) authInitial := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (AuthorizationPointFrame407.completed_point original c w authInitial initial senderInitial receiverInitial ⟨0,by decide⟩).trans
      (congrArg Group.Point.x binding).symm
  · exact (AuthorizationPointFrame407.completed_point original c w authInitial initial senderInitial receiverInitial ⟨1,by decide⟩).trans
      (congrArg Group.Point.y binding).symm
  · exact AuthorizationPointFrame407.completed_point original c w authInitial initial senderInitial receiverInitial ⟨2,by decide⟩
  · exact AuthorizationPointFrame407.completed_point original c w authInitial initial senderInitial receiverInitial ⟨3,by decide⟩
  · intro index before
    have cases : index=0 ∨ index=1 ∨ index=2 := by omega
    rcases cases with rfl|rfl|rfl
    · exact AuthorizationPointFrame407.completed_point original c w authInitial initial senderInitial receiverInitial ⟨4,by decide⟩
    · exact AuthorizationPointFrame407.completed_point original c w authInitial initial senderInitial receiverInitial ⟨5,by decide⟩
    · exact AuthorizationPointFrame407.completed_point original c w authInitial initial senderInitial receiverInitial ⟨6,by decide⟩

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (valid : Group.OnCurve (CapturedFirstSubgroup81.d:F) authInitial)
    (binding : CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) authInitial=SubgroupSeedCompletion203.fieldPoint w.auth.ak) :
    CompilerAssertionBlock51.SatisfiesAt
      (SemanticWordFrame373.assignment (AuthorizationPointSeed405.seed original w authInitial) c w initial senderInitial receiverInitial)
      (fun index => CapturedFullRelation58.rowAt (179933+index)) 6 := by
  let source := EncodedWordBits375.base (AuthorizationPointSeed405.seed original w authInitial) w senderInitial receiverInitial
  let rho := SemanticWordFrame373.assignment (AuthorizationPointSeed405.seed original w authInitial) c w initial senderInitial receiverInitial
  have zero := SharedHighZeroRows333.zero (UserWordSeed342.seed source w) c w initial
  have linked := SharedComparisonBlocks327.linked (HighZeroSeed329.seed (UserWordSeed342.seed source w) w) c w initial
  have arithmetic := SharedHighZeroRows333.arithmetic (UserWordSeed342.seed source w) c w initial
  change rho 0=1 at zero
  change rho copy=rho 0 at linked
  change CompilerAssertionBlock51.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954 at arithmetic
  exact AuthorizationSubgroupCapture409B05.complete rho authInitial ConcreteJubjubField01.imaginary zero linked arithmetic
    (input_roles original c w authInitial initial senderInitial receiverInitial binding) valid
    (by rw [coefficient_eq]; exact ConcreteJubjubField01.coefficient_no_unit_square) ConcreteJubjubField01.imaginary_square

end ShielddSecurity.SharedAuthorizationSubgroup410

set_option pp.all true in
#check @ShielddSecurity.SharedAuthorizationSubgroup410.input_roles
#print axioms ShielddSecurity.SharedAuthorizationSubgroup410.input_roles

set_option pp.all true in
#check @ShielddSecurity.SharedAuthorizationSubgroup410.all_rows
#print axioms ShielddSecurity.SharedAuthorizationSubgroup410.all_rows
