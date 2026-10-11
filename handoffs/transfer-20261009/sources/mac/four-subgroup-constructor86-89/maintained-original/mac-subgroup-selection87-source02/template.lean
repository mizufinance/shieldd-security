import ShielddSecurity.CapturedFourSubgroups82
import ShielddSecurity.CapturedFirstSubgroupSeed85
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedSubgroupSelection87
open Compiler
def rename (group : Fin 4) : Nat → Nat :=
  if before : group.val=0 then id else CapturedFourSubgroups82.rename ⟨group.val-1,by omega⟩
def arithmeticRows (group : Fin 4) : List Row :=
  CompilerColumnRenaming05.rows (rename group) TransferFirstSubgroupData01.arithmeticRows.toList
noncomputable def check (group : Fin 4) : Bool :=
  (List.range 64).all (fun index => decide (CapturedFullArithmetic52.rowAt (group.val*64+index)=(arithmeticRows group)[index]?)) &&
  decide ((arithmeticRows group)[64]?=some ⟨[(0,1),(TransferFirstSubgroupData01.copy,-1)],[]⟩) &&
  decide ((arithmeticRows group).length=65)
theorem checked0 : check ⟨0,by decide⟩=true := by decide +kernel
theorem checked1 : check ⟨1,by decide⟩=true := by decide +kernel
theorem checked2 : check ⟨2,by decide⟩=true := by decide +kernel
theorem checked3 : check ⟨3,by decide⟩=true := by decide +kernel
theorem checked (group : Fin 4) : check group=true := by
  rcases group with ⟨group,bound⟩
  interval_cases group
  · exact checked0
  · exact checked1
  · exact checked2
  · exact checked3
variable {F : Type} [Field F]
theorem from_arithmetic (rho : Nat → F) (group : Fin 4)
    (sat : CompilerArithmeticBlock44.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (linked : rho TransferFirstSubgroupData01.copy=rho 0) : Satisfies rho (arithmeticRows group) := by
  have checks:=Bool.and_eq_true_iff.mp (checked group)
  have data:=Bool.and_eq_true_iff.mp checks.1
  have length:=of_decide_eq_true checks.2
  intro row member
  obtain ⟨index,found⟩:=List.mem_iff_getElem?.mp member
  obtain ⟨before,_⟩:=List.getElem?_eq_some_iff.mp found
  have bound : index<65 := by omega
  by_cases arithmetic:index<64
  · have same:=of_decide_eq_true (List.all_eq_true.mp data.1 index (List.mem_range.mpr arithmetic))
    exact sat (group.val*64+index) (by omega) row (same.trans found)
  · have eqIndex:index=64 := by omega
    subst index
    have same:=Option.some.inj ((of_decide_eq_true data.2).symm.trans found)
    subst row
    simp [eval,linked,Square]
theorem pulled (rho : Nat → F) (group : Fin 4)
    (sat : CompilerArithmeticBlock44.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (linked : rho TransferFirstSubgroupData01.copy=rho 0) :
    Satisfies (fun column => rho (rename group column)) TransferFirstSubgroupData01.arithmeticRows.toList :=
  (CompilerColumnRenaming05.satisfies_rows (rename group) rho _).mp (from_arithmetic rho group sat linked)
end ShielddSecurity.CapturedSubgroupSelection87
