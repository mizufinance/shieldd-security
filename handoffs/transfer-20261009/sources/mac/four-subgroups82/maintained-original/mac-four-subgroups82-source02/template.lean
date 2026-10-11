import ShielddSecurity.CapturedFirstSubgroup81
import ShielddSecurity.CapturedInitial73419Subgroups01
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedFourSubgroups82
open Compiler
namespace D
private abbrev p := TransferFirstSubgroupData01.p
private abbrev d := CapturedFirstSubgroup81.d
private abbrev negative := CapturedFirstSubgroup81.negative
private abbrev rows := CapturedFirstSubgroup81.rows
end D
-- These swaps are qualified injective permutations; row soundness itself needs no injectivity.
def rename (group : Fin 3) : Nat → Nat :=
  match group.val with
  | 0 => CapturedInitial73419Subgroups01.rename1
  | 1 => CapturedInitial73419Subgroups01.rename2
  | _ => CapturedInitial73419Subgroups01.rename3
def position (group : Fin 3) (index : Nat) : Nat :=
  if index<64 then (group.val+1)*64+index
  else if index<70 then 177955+(group.val+1)*6+(index-64)
  else 200769
def rows (group : Fin 3) : List Row := CompilerColumnRenaming05.rows (rename group) D.rows
def check : Bool := (List.finRange 3).all (fun group =>
  (List.range (rows group).length).all (fun index =>
    decide (position group index<200770) &&
    decide (CapturedFullRelation58.rowAt (position group index)=(rows group)[index]?)))
theorem checked : check=true := by decide +kernel
variable {F : Type} [Field F]
theorem selected (rho : Nat → F) (group : Fin 3)
    (sat : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    Satisfies rho (rows group) := by
  intro row member
  obtain ⟨index,found⟩:=List.mem_iff_getElem?.mp member
  obtain ⟨before,_⟩:=List.getElem?_eq_some_iff.mp found
  have all:=List.all_eq_true.mp checked group (List.mem_finRange group)
  have good:=Bool.and_eq_true_iff.mp (List.all_eq_true.mp all index (List.mem_range.mpr before))
  exact sat (position group index) (of_decide_eq_true good.1) row
    ((of_decide_eq_true good.2).trans found)
theorem zero_fixed (group : Fin 3) : rename group 0=0 := by
  rcases group with ⟨group,bound⟩
  interval_cases group <;> rfl
def preimage (rho : Nat → F) (group : Fin 3) : Group.Point F :=
  ⟨rho (rename group 16),rho (rename group 17)⟩
def point (rho : Nat → F) (group : Fin 3) : Group.Point F :=
  ⟨rho (rename group 14),rho (rename group 15)⟩
variable [CharP F D.p]
theorem source (rho : Nat → F) (one : rho 0=1) (group : Fin 3)
    (sat : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    Group.OnCurve (D.d:F) (preimage rho group) ∧
      CompilerSubgroupArithmetic79.eight (D.d:F) (preimage rho group)=point rho group := by
  let pulled := fun column => rho (rename group column)
  have pullrows : Satisfies pulled D.rows :=
    (CompilerColumnRenaming05.satisfies_rows (rename group) rho D.rows).mp (selected rho group sat)
  have pullone : pulled 0=1 := by simpa only [pulled,zero_fixed] using one
  have actual:=TransferFirstSubgroupCertificates01.arbitrary_assignment_sound pulled pullone
    (CompilerArithmeticTransport41.four_ne_zero (F:=F)) pullrows
  have result:=CompilerSubgroupSource80.graph_assertions_sound
    TransferFirstSubgroupData01.graph D.d D.negative
    (fun input => eval pulled (TransferFirstSubgroupData01.inputTerms input))
    (CompilerSubgroupSource80.modulus_negative_one (F:=F)) CapturedFirstSubgroup81.shape actual.2
  simpa only [CompilerSubgroupSource80.preimage,CompilerSubgroupSource80.point,
    TransferFirstSubgroupData01.inputTerms,eval,List.foldl_cons,List.foldl_nil,
    Int.cast_one,one_mul,zero_add,add_zero,pulled,preimage,point] using result
theorem all_four (rho : Nat → F) (one : rho 0=1)
    (sat : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    (Group.OnCurve (D.d:F) (⟨rho 16,rho 17⟩ : Group.Point F) ∧
      CompilerSubgroupArithmetic79.eight (D.d:F) ⟨rho 16,rho 17⟩=⟨rho 14,rho 15⟩) ∧
    (Group.OnCurve (D.d:F) (⟨rho 25,rho 26⟩ : Group.Point F) ∧
      CompilerSubgroupArithmetic79.eight (D.d:F) ⟨rho 25,rho 26⟩=⟨rho 23,rho 24⟩) ∧
    (Group.OnCurve (D.d:F) (⟨rho 37,rho 38⟩ : Group.Point F) ∧
      CompilerSubgroupArithmetic79.eight (D.d:F) ⟨rho 37,rho 38⟩=⟨rho 35,rho 36⟩) ∧
    (Group.OnCurve (D.d:F) (⟨rho 44,rho 45⟩ : Group.Point F) ∧
      CompilerSubgroupArithmetic79.eight (D.d:F) ⟨rho 44,rho 45⟩=⟨rho 42,rho 43⟩) := by
  exact ⟨CapturedFirstSubgroup81.full_source rho one sat,
    source rho one ⟨0,by decide⟩ sat,source rho one ⟨1,by decide⟩ sat,source rho one ⟨2,by decide⟩ sat⟩
end ShielddSecurity.CapturedFourSubgroups82
