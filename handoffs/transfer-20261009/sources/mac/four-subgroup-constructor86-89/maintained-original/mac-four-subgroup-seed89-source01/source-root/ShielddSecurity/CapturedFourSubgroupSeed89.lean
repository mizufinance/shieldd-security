import ShielddSecurity.CapturedFourSubgroupConstructor88
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedFourSubgroupSeed89
open Compiler
variable {F : Type} [Field F]
def seeded (base : Nat → F) (initial : Fin 4 → Group.Point F) (column : Nat) : F :=
  if column=16 then (initial ⟨0,by decide⟩).x
  else if column=17 then (initial ⟨0,by decide⟩).y
  else if column=18 then CompilerSubgroupArithmetic79.hints (CapturedFirstSubgroup81.d:F) (initial ⟨0,by decide⟩) 0
  else if column=19 then CompilerSubgroupArithmetic79.hints (CapturedFirstSubgroup81.d:F) (initial ⟨0,by decide⟩) 1
  else if column=20 then CompilerSubgroupArithmetic79.hints (CapturedFirstSubgroup81.d:F) (initial ⟨0,by decide⟩) 2
  else if column=25 then (initial ⟨1,by decide⟩).x
  else if column=26 then (initial ⟨1,by decide⟩).y
  else if column=27 then CompilerSubgroupArithmetic79.hints (CapturedFirstSubgroup81.d:F) (initial ⟨1,by decide⟩) 0
  else if column=28 then CompilerSubgroupArithmetic79.hints (CapturedFirstSubgroup81.d:F) (initial ⟨1,by decide⟩) 1
  else if column=29 then CompilerSubgroupArithmetic79.hints (CapturedFirstSubgroup81.d:F) (initial ⟨1,by decide⟩) 2
  else if column=37 then (initial ⟨2,by decide⟩).x
  else if column=38 then (initial ⟨2,by decide⟩).y
  else if column=39 then CompilerSubgroupArithmetic79.hints (CapturedFirstSubgroup81.d:F) (initial ⟨2,by decide⟩) 0
  else if column=40 then CompilerSubgroupArithmetic79.hints (CapturedFirstSubgroup81.d:F) (initial ⟨2,by decide⟩) 1
  else if column=41 then CompilerSubgroupArithmetic79.hints (CapturedFirstSubgroup81.d:F) (initial ⟨2,by decide⟩) 2
  else if column=44 then (initial ⟨3,by decide⟩).x
  else if column=45 then (initial ⟨3,by decide⟩).y
  else if column=46 then CompilerSubgroupArithmetic79.hints (CapturedFirstSubgroup81.d:F) (initial ⟨3,by decide⟩) 0
  else if column=47 then CompilerSubgroupArithmetic79.hints (CapturedFirstSubgroup81.d:F) (initial ⟨3,by decide⟩) 1
  else if column=48 then CompilerSubgroupArithmetic79.hints (CapturedFirstSubgroup81.d:F) (initial ⟨3,by decide⟩) 2
  else base column
def hintColumns : List Nat := [16,17,18,19,20,25,26,27,28,29,37,38,39,40,41,44,45,46,47,48]
theorem seeded_outside (base : Nat → F) (initial : Fin 4 → Group.Point F) (column : Nat)
    (outside : column∉hintColumns) : seeded base initial column=base column := by
  simp only [hintColumns,List.mem_cons,List.not_mem_nil,or_false,not_or] at outside
  simp only [seeded,if_neg outside.1,if_neg outside.2.1,if_neg outside.2.2.1,
    if_neg outside.2.2.2.1,if_neg outside.2.2.2.2.1,
    if_neg outside.2.2.2.2.2.1,if_neg outside.2.2.2.2.2.2.1,
    if_neg outside.2.2.2.2.2.2.2.1,if_neg outside.2.2.2.2.2.2.2.2.1,
    if_neg outside.2.2.2.2.2.2.2.2.2.1,if_neg outside.2.2.2.2.2.2.2.2.2.2.1,
    if_neg outside.2.2.2.2.2.2.2.2.2.2.2.1,if_neg outside.2.2.2.2.2.2.2.2.2.2.2.2.1,
    if_neg outside.2.2.2.2.2.2.2.2.2.2.2.2.2.1,if_neg outside.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    if_neg outside.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,if_neg outside.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    if_neg outside.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,if_neg outside.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    if_neg outside.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]
def Claimed (base : Nat → F) (group : Fin 4) : Group.Point F :=
  ⟨base (CapturedSubgroupSelection87.rename group 14),base (CapturedSubgroupSelection87.rename group 15)⟩
theorem seeded_roles (base : Nat → F) (initial : Fin 4 → Group.Point F) (group : Fin 4)
    (binding : Claimed base group=CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) (initial group)) :
    CapturedFourSubgroupConstructor88.InputRoles
      (fun column => seeded base initial (CapturedSubgroupSelection87.rename group column)) (initial group) := by
  rcases group with ⟨group,bound⟩
  interval_cases group
  · refine ⟨?_,?_,?_,?_,?_⟩
    · exact congrArg Group.Point.x binding
    · exact congrArg Group.Point.y binding
    · rfl
    · rfl
    · intro index before
      interval_cases index <;> rfl
  · refine ⟨?_,?_,?_,?_,?_⟩
    · exact congrArg Group.Point.x binding
    · exact congrArg Group.Point.y binding
    · rfl
    · rfl
    · intro index before
      interval_cases index <;> rfl
  · refine ⟨?_,?_,?_,?_,?_⟩
    · exact congrArg Group.Point.x binding
    · exact congrArg Group.Point.y binding
    · rfl
    · rfl
    · intro index before
      interval_cases index <;> rfl
  · refine ⟨?_,?_,?_,?_,?_⟩
    · exact congrArg Group.Point.x binding
    · exact congrArg Group.Point.y binding
    · rfl
    · rfl
    · intro index before
      interval_cases index <;> rfl
variable [CharP F TransferFirstSubgroupData01.p]
def completed (base : Nat → F) (initial : Fin 4 → Group.Point F) : Nat → F :=
  CapturedFullArithmetic52.completed (seeded base initial)
theorem arithmetic (base : Nat → F) (initial : Fin 4 → Group.Point F) :
    CompilerArithmeticBlock44.SatisfiesAt (completed base initial) CapturedFullArithmetic52.rowAt 177954 :=
  CapturedFullArithmetic52.complete (seeded base initial)
omit [CharP F TransferFirstSubgroupData01.p] in
theorem outside (base : Nat → F) (initial : Fin 4 → Group.Point F) (column : Nat)
    (unwritten : column<22738 ∨ 200692≤column) (unseeded : column∉hintColumns) :
    completed base initial column=base column :=
  (CapturedFullArithmetic52.outside (seeded base initial) column unwritten).trans (seeded_outside base initial column unseeded)
theorem completed_roles (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (binding : ∀ group,Claimed base group=CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) (initial group)) :
    ∀ group,CapturedFourSubgroupConstructor88.InputRoles
      (fun column => completed base initial (CapturedSubgroupSelection87.rename group column)) (initial group) := by
  intro group
  have roles:=seeded_roles base initial group (binding group)
  have fixed (index : Nat) (small : 14≤index ∧ index≤20) :
      completed base initial (CapturedSubgroupSelection87.rename group index)=
      seeded base initial (CapturedSubgroupSelection87.rename group index) := by
    apply CapturedFullArithmetic52.outside
    rcases group with ⟨group,bound⟩
    interval_cases group <;> simp [CapturedSubgroupSelection87.rename,CapturedFourSubgroups82.rename,
      CompilerWindowRenaming05.swap] <;> omega
  refine ⟨(fixed 14 (by omega)).trans roles.1,(fixed 15 (by omega)).trans roles.2.1,
    (fixed 16 (by omega)).trans roles.2.2.1,(fixed 17 (by omega)).trans roles.2.2.2.1,?_⟩
  intro index before
  exact (fixed (18+index) (by omega)).trans (roles.2.2.2.2 index before)
theorem all_four (base : Nat → F) (initial : Fin 4 → Group.Point F) (imaginary : F)
    (one : base 0=1) (linked : base TransferFirstSubgroupData01.copy=base 0)
    (binding : ∀ group,Claimed base group=CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) (initial group))
    (valid : ∀ group,Group.OnCurve (CapturedFirstSubgroup81.d:F) (initial group))
    (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F)) (imaginarySquare : imaginary*imaginary=-1) :
    ∀ group,Satisfies (completed base initial) (CapturedFourSubgroupConstructor88.originalRows group) := by
  have zero:=outside base initial 0 (by omega) (by decide)
  have copy:=outside base initial TransferFirstSubgroupData01.copy (by decide) (by decide)
  exact CapturedFourSubgroupConstructor88.all_four (completed base initial) initial imaginary
    (zero.trans one) (copy.trans (linked.trans zero.symm)) (arithmetic base initial)
    (completed_roles base initial binding) valid nonSquare imaginarySquare
end ShielddSecurity.CapturedFourSubgroupSeed89

set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroupSeed89.seeded
#print axioms ShielddSecurity.CapturedFourSubgroupSeed89.seeded
set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroupSeed89.hintColumns
#print axioms ShielddSecurity.CapturedFourSubgroupSeed89.hintColumns
set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroupSeed89.seeded_outside
#print axioms ShielddSecurity.CapturedFourSubgroupSeed89.seeded_outside
set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroupSeed89.Claimed
#print axioms ShielddSecurity.CapturedFourSubgroupSeed89.Claimed
set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroupSeed89.seeded_roles
#print axioms ShielddSecurity.CapturedFourSubgroupSeed89.seeded_roles
set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroupSeed89.completed
#print axioms ShielddSecurity.CapturedFourSubgroupSeed89.completed
set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroupSeed89.arithmetic
#print axioms ShielddSecurity.CapturedFourSubgroupSeed89.arithmetic
set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroupSeed89.outside
#print axioms ShielddSecurity.CapturedFourSubgroupSeed89.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroupSeed89.completed_roles
#print axioms ShielddSecurity.CapturedFourSubgroupSeed89.completed_roles
set_option pp.all true in
#check @ShielddSecurity.CapturedFourSubgroupSeed89.all_four
#print axioms ShielddSecurity.CapturedFourSubgroupSeed89.all_four
