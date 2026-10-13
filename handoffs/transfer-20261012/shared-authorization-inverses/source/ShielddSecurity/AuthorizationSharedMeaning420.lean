import ShielddSecurity.AuthorizationSharedOperands420E
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationSharedMeaning420
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

open AuthorizationSharedFrame420B

theorem operands (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (index : Fin 5) :
    eval (assignment original c w authInitial initial senderInitial receiverInitial)
      (CapturedAuthorizationShared419.operandTerms index.val)=AuthorizationSharedDomain415.operand c w index := by
  let base := originalBase original c w authInitial senderInitial receiverInitial
  let rho := assignment original c w authInitial initial senderInitial receiverInitial
  have arithmetic := AuthorizationSharedFrame420B.arithmetic original c w authInitial initial senderInitial receiverInitial
  have copied := AuthorizationSharedCopy420C.copied original c w authInitial initial senderInitial receiverInitial
  change rho copy=1 at copied
  have user := AuthorizationSharedUser420D.user_value original c w authInitial initial senderInitial receiverInitial
  have asset : rho 6=(w.asset:F) := SharedRegulatedValue316.asset_meaning base c w initial
  have flagValue : rho 10=(if w.regulated then 1 else 0) := SharedRegulatedValue316.control_meaning base c w initial
  have ringInput : rho 23=(w.registry.ring.x:F) :=
    (SharedRegulatedValue316.original_frame base c w initial 23 (by constructor <;> decide) (by decide)).trans
      ((RegisteredConstructorFrame309.prepared_outside base c w 23 (by decide) (by constructor <;> decide)).trans
        (RegistryNaturalSeed298.seed_fixed _ _ 23 (by decide)))
  exact AuthorizationSharedOperands420E.operands rho c w arithmetic copied user asset flagValue ringInput index
end ShielddSecurity.AuthorizationSharedMeaning420

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSharedMeaning420.operands
#print axioms ShielddSecurity.AuthorizationSharedMeaning420.operands
