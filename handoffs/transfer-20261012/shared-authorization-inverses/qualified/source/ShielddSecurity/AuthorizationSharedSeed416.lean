import ShielddSecurity.AuthorizationSharedDomain415
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationSharedSeed416
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def seed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) (column : Nat) : F :=
  if h : 1988≤column ∧ column<1993 then
    (AuthorizationSharedDomain415.operand c w ⟨column-1988,by omega⟩)⁻¹
  else original column

theorem outside (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) (column : Nat)
    (out : ¬(1988≤column ∧ column<1993)) : seed original c w column=original column := by
  simp only [seed,dif_neg out]

theorem value (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) (index : Fin 5) :
    seed original c w (1988+index.val)=(AuthorizationSharedDomain415.operand c w index)⁻¹ := by
  have inside : 1988≤1988+index.val ∧1988+index.val<1993 := by have := index.isLt; omega
  simp only [seed,dif_pos inside,Nat.add_sub_cancel_left]

end ShielddSecurity.AuthorizationSharedSeed416

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSharedSeed416.seed
#print axioms ShielddSecurity.AuthorizationSharedSeed416.seed

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSharedSeed416.outside
#print axioms ShielddSecurity.AuthorizationSharedSeed416.outside

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSharedSeed416.value
#print axioms ShielddSecurity.AuthorizationSharedSeed416.value
