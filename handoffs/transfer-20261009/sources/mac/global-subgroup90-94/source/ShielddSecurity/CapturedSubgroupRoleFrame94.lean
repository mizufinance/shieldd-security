import ShielddSecurity.CapturedGlobalPosition77
import ShielddSecurity.CapturedSubgroupFrame92
import ShielddSecurity.CapturedFourSubgroupConstructor88
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedSubgroupRoleFrame94
variable {F : Type} [Field F]
theorem column (base : Nat → F) (epoch position : Nat) (group : Fin 4) (index : Nat)
    (lower : 14≤index) (upper : index≤20) :
    CapturedGlobalPosition77.completed base epoch position (CapturedSubgroupSelection87.rename group index)=
      base (CapturedSubgroupSelection87.rename group index) := by
  have safe:=CapturedSubgroupFrame92.safe group index lower upper
  exact CapturedGlobalPosition77.outside base epoch position (CapturedSubgroupSelection87.rename group index)
    (Or.inl safe.1) ⟨safe.2.1,safe.2.2.1,safe.2.2.2.1⟩ safe.2.2.2.2.1 (Or.inl safe.2.2.2.2.2)
theorem transport (rho sigma : Nat → F) (initial : Group.Point F)
    (same : ∀ index,14≤index → index≤20 → rho index=sigma index)
    (roles : CapturedFourSubgroupConstructor88.InputRoles sigma initial) :
    CapturedFourSubgroupConstructor88.InputRoles rho initial := by
  refine ⟨(same 14 (by decide) (by decide)).trans roles.1,
    (same 15 (by decide) (by decide)).trans roles.2.1,
    (same 16 (by decide) (by decide)).trans roles.2.2.1,
    (same 17 (by decide) (by decide)).trans roles.2.2.2.1,?_⟩
  intro index before
  exact (same (18+index) (Nat.le_trans (by decide) (Nat.le_add_right 18 index))
    (Nat.add_le_add_left (Nat.le_of_lt_succ before) 18)).trans (roles.2.2.2.2 index before)
end ShielddSecurity.CapturedSubgroupRoleFrame94

set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupRoleFrame94.column
#print axioms ShielddSecurity.CapturedSubgroupRoleFrame94.column
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupRoleFrame94.transport
#print axioms ShielddSecurity.CapturedSubgroupRoleFrame94.transport
