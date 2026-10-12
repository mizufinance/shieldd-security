import ShielddSecurity.RegistrySeedFrame265
import ShielddSecurity.CapturedFourSubgroupSeed89
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedSubgroups269
open Compiler CompilerArithmeticTransport41 PoseidonNatural192
theorem hint_checked : CapturedFourSubgroupSeed89.hintColumns.all (fun column => decide (column<49))=true := by decide +kernel
theorem hint_small (column : Nat) (member : column∈CapturedFourSubgroupSeed89.hintColumns) : column<49 :=
 of_decide_eq_true (List.all_eq_true.mp hint_checked column member)
theorem renamed_roles (group : Fin 4) (index : Nat) (bounds : 14≤index ∧ index≤20) :
 RegistrySeedFrame265.Protected (CapturedSubgroupSelection87.rename group index) := by
 rcases group with ⟨group,before⟩
 rcases bounds with ⟨lower,upper⟩
 interval_cases index <;> interval_cases group <;>
 norm_num [RegistrySeedFrame265.Protected,CapturedSubgroupSelection87.rename,CapturedFourSubgroups82.rename,CompilerWindowRenaming05.swap]
variable {F : Type} [Field F]
theorem completed_roles (base : Nat → F) (initial : Fin 4 → Group.Point F)
 (numbers : Nat → Nat) (fallback : Nat → Bool)
 (binding : ∀ group,CapturedFourSubgroupSeed89.Claimed base group=CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) (initial group)) :
 ∀ group,CapturedFourSubgroupConstructor88.InputRoles
 (fun column => SharedWordWitness221.completed (CapturedFourSubgroupSeed89.seeded base initial) numbers fallback (CapturedSubgroupSelection87.rename group column)) (initial group) := by
 intro group
 have roles:=CapturedFourSubgroupSeed89.seeded_roles base initial group (binding group)
 have fixed (index : Nat) (bounds : 14≤index ∧ index≤20) :=
   RegistrySeedFrame265.completed_frame (CapturedFourSubgroupSeed89.seeded base initial) numbers fallback
     (CapturedSubgroupSelection87.rename group index) (renamed_roles group index bounds)
 refine ⟨(fixed 14 (by omega)).trans roles.1,(fixed 15 (by omega)).trans roles.2.1,
   (fixed 16 (by omega)).trans roles.2.2.1,(fixed 17 (by omega)).trans roles.2.2.2.1,?_⟩
 intro index before
 exact (fixed (18+index) (by omega)).trans (roles.2.2.2.2 index before)
variable [CharP F p]
theorem all_four (base : Nat → F) (initial : Fin 4 → Group.Point F)
 (numbers : Nat → Nat) (fallback : Nat → Bool) (imaginary : F) (one : base 0=1)
 (binding : ∀ group,CapturedFourSubgroupSeed89.Claimed base group=CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) (initial group))
 (valid : ∀ group,Group.OnCurve (CapturedFirstSubgroup81.d:F) (initial group))
 (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F)) (imaginarySquare : imaginary*imaginary = -1) :
 ∀ group,Satisfies (SharedWordWitness221.completed (CapturedFourSubgroupSeed89.seeded base initial) numbers fallback)
   (CapturedFourSubgroupConstructor88.originalRows group) := by
 let raw:=CapturedFourSubgroupSeed89.seeded base initial
 have originalZero : raw 0=base 0 := CapturedFourSubgroupSeed89.seeded_outside base initial 0 (by decide)
 have zero:=CapturedFullRelation58.candidate_outside (SharedWordWitness221.seeded raw numbers fallback) 0 (by omega) (by decide)
 have fixedZero:=SharedWordWitness221.seeded_fixed raw numbers fallback
 exact CapturedFourSubgroupConstructor88.all_four (SharedWordWitness221.completed raw numbers fallback) initial imaginary
   (zero.trans (fixedZero.1.trans (originalZero.trans one)))
   (CapturedFullRelation58.candidate_links (SharedWordWitness221.seeded raw numbers fallback)).2.2
   (SharedWordWitness221.arithmetic raw numbers fallback)
   (completed_roles base initial numbers fallback binding) valid nonSquare imaginarySquare
omit [CharP F p] in
theorem recover_frame (representation : CanonicalRepresentation F) (base : Nat → F)
 (initial : Fin 4 → Group.Point F) :
 RegistryRecovery194.recover representation (CapturedFourSubgroupSeed89.seeded base initial)=RegistryRecovery194.recover representation base := by
 unfold RegistryRecovery194.recover
 simp only [CapturedFourSubgroupSeed89.seeded_outside base initial 11 (by decide),CapturedFourSubgroupSeed89.seeded_outside base initial 12 (by decide),CapturedFourSubgroupSeed89.seeded_outside base initial 13 (by decide),CapturedFourSubgroupSeed89.seeded_outside base initial 14 (by decide),CapturedFourSubgroupSeed89.seeded_outside base initial 15 (by decide),CapturedFourSubgroupSeed89.seeded_outside base initial 21 (by decide),CapturedFourSubgroupSeed89.seeded_outside base initial 22 (by decide),CapturedFourSubgroupSeed89.seeded_outside base initial 23 (by decide),CapturedFourSubgroupSeed89.seeded_outside base initial 24 (by decide),CapturedFourSubgroupSeed89.seeded_outside base initial 30 (by decide),CapturedFourSubgroupSeed89.seeded_outside base initial 31 (by decide),CapturedFourSubgroupSeed89.seeded_outside base initial 32 (by decide),CapturedFourSubgroupSeed89.seeded_outside base initial 33 (by decide),CapturedFourSubgroupSeed89.seeded_outside base initial 34 (by decide),CapturedFourSubgroupSeed89.seeded_outside base initial 35 (by decide),CapturedFourSubgroupSeed89.seeded_outside base initial 36 (by decide),CapturedFourSubgroupSeed89.seeded_outside base initial 42 (by decide),CapturedFourSubgroupSeed89.seeded_outside base initial 43 (by decide),CapturedFourSubgroupSeed89.seeded_outside base initial 135 (by decide)]
 congr 1
 funext level slot
 apply congrArg representation.value
 apply CapturedFourSubgroupSeed89.seeded_outside
 intro member
 have small:=hint_small (136+3*level.val+slot.val) member
 omega
omit [CharP F p] in
theorem anchor_frame (representation : CanonicalRepresentation F) (base : Nat → F)
 (initial : Fin 4 → Group.Point F) :
 representation.value (CapturedFourSubgroupSeed89.seeded base initial 4)=representation.value (base 4) :=
 congrArg representation.value (CapturedFourSubgroupSeed89.seeded_outside base initial 4 (by decide))
end ShielddSecurity.SharedSubgroups269

set_option pp.all true in
#check @ShielddSecurity.SharedSubgroups269.hint_checked
#print axioms ShielddSecurity.SharedSubgroups269.hint_checked
set_option pp.all true in
#check @ShielddSecurity.SharedSubgroups269.hint_small
#print axioms ShielddSecurity.SharedSubgroups269.hint_small
set_option pp.all true in
#check @ShielddSecurity.SharedSubgroups269.renamed_roles
#print axioms ShielddSecurity.SharedSubgroups269.renamed_roles
set_option pp.all true in
#check @ShielddSecurity.SharedSubgroups269.completed_roles
#print axioms ShielddSecurity.SharedSubgroups269.completed_roles
set_option pp.all true in
#check @ShielddSecurity.SharedSubgroups269.all_four
#print axioms ShielddSecurity.SharedSubgroups269.all_four
set_option pp.all true in
#check @ShielddSecurity.SharedSubgroups269.recover_frame
#print axioms ShielddSecurity.SharedSubgroups269.recover_frame
set_option pp.all true in
#check @ShielddSecurity.SharedSubgroups269.anchor_frame
#print axioms ShielddSecurity.SharedSubgroups269.anchor_frame
