import ShielddSecurity.AuthorizationSharedUser420D
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationSharedOperands420E
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

theorem operands (rho : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (arithmetic : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (copied : rho copy=1)
    (user : ∀ slot : Fin 3, rho (1504+8*slot.val)=((UserPointDomain351.point w.sender slot).x:F))
    (asset : rho 6=(w.asset:F)) (flagValue : rho 10=(if w.regulated then 1 else 0))
    (ringInput : rho 23=(w.registry.ring.x:F)) (index : Fin 5) :
    eval rho (CapturedAuthorizationShared419.operandTerms index.val)=AuthorizationSharedDomain415.operand c w index := by
  rcases index with ⟨index,bound⟩
  have cases : index=0 ∨ index=1 ∨ index=2 ∨ index=3 ∨ index=4 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl
  · change (1:F)*rho 1504+0=_
    simpa only [one_mul,add_zero] using user ⟨0,by decide⟩
  · change (1:F)*rho 1512+0=_
    simpa only [one_mul,add_zero] using user ⟨1,by decide⟩
  · change (1:F)*rho 1520+0=_
    simpa only [one_mul,add_zero] using user ⟨2,by decide⟩
  · change (49822839976625491399435002605169580882773999909559575334089637637825427273330:F)*rho copy+((1:F)*rho 33796+0)=((ring (crypto c) w).x:F)
    rw [AuthorizationRingProduct420A.ring_product rho arithmetic,copied,ringInput,flagValue]
    cases flag : w.regulated with
    | false =>
      simp only [ring,flag,Bool.false_eq_true,if_false,mul_one,zero_mul,one_mul,add_zero]
      rfl
    | true =>
      simp only [ring,flag,if_true,mul_one,one_mul,add_zero]
      ring
  · change (1:F)*rho 6+0=(w.asset:F)
    simpa only [one_mul,add_zero] using asset
end ShielddSecurity.AuthorizationSharedOperands420E
set_option pp.all true in
#check @ShielddSecurity.AuthorizationSharedOperands420E.operands
#print axioms ShielddSecurity.AuthorizationSharedOperands420E.operands
