import ShielddSecurity.CapturedMerkleIntegerRoot191
import ShielddSecurity.RegistryRecovery194
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleFieldFold196
variable {F : Type} [Field F]
open CapturedMerkleIntegerRoot191
omit [Field F] in
theorem fold_congr (items : List Nat) (left right : F → Nat → F)
 (equal : ∀ level ∈ items, ∀ node, left node level=right node level) (initial : F) :
 items.foldl left initial=items.foldl right initial := by
 induction items generalizing initial with
 | nil => rfl
 | cons head tail ih =>
   simp only [List.foldl_cons]
   rw [equal head (by simp) initial]
   exact ih (fun level member node => equal level (by simp only [List.mem_cons];exact Or.inr member) node) _
def fieldStep (rho : Nat → F) (position : Nat) (node : F) (level : Nat) : F :=
 let slot:=position/4^level%4
 let a:=rho (136+3*level)
 let b:=rho (136+3*level+1)
 let c:=rho (136+3*level+2)
 let xs:=if slot=0 then [node,a,b,c] else if slot=1 then [a,node,b,c]
   else if slot=2 then [a,b,node,c] else [a,b,c,node]
 Poseidon.hash RegistryNatural193.small RegistryNatural193.wide 2
   ([((level+1:Nat):F)]++xs)
theorem field_step (rho : Nat → F) (position : Nat) (level : Fin 16) (node : F) :
 fieldStep rho position node level.val=step rho position level node := by
 have b : 136+3*level.val+1=137+3*level.val := by omega
 have c : 136+3*level.val+2=138+3*level.val := by omega
 simp only [fieldStep,step,RegistryNatural193.wide,b,c,children]
 split_ifs <;> rfl
theorem root_fold (rho : Nat → F) (position count : Nat) :
 root rho position count=(List.range count).foldl
   (fun node level => step rho position ⟨level%16,Nat.mod_lt level (by decide)⟩ node)
   (MerkleInputMeaning28.registryMeaning rho) := by
 induction count with
 | zero => rfl
 | succ count ih =>
   rw [root,ih,List.range_succ,List.foldl_append]
   rfl
theorem field_root (rho : Nat → F) (position : Nat) :
 PoseidonNatural192.treeRoot RegistryNatural193.small RegistryNatural193.wide .asset 16 position
   (MerkleInputMeaning28.registryMeaning rho) (fun level slot => rho (136+3*level+slot.val))=
 root rho position 16 := by
 rw [root_fold]
 change (List.range 16).foldl (fieldStep rho position) _=_
 apply fold_congr
 intro level member node
 have bound : level<16 := List.mem_range.mp member
 have reduce : level%16=level := Nat.mod_eq_of_lt bound
 simpa only [reduce] using field_step rho position ⟨level,bound⟩ node
end ShielddSecurity.MerkleFieldFold196

set_option pp.all true in
#check @ShielddSecurity.MerkleFieldFold196.fold_congr
#print axioms ShielddSecurity.MerkleFieldFold196.fold_congr
set_option pp.all true in
#check @ShielddSecurity.MerkleFieldFold196.fieldStep
#print axioms ShielddSecurity.MerkleFieldFold196.fieldStep
set_option pp.all true in
#check @ShielddSecurity.MerkleFieldFold196.field_step
#print axioms ShielddSecurity.MerkleFieldFold196.field_step
set_option pp.all true in
#check @ShielddSecurity.MerkleFieldFold196.root_fold
#print axioms ShielddSecurity.MerkleFieldFold196.root_fold
set_option pp.all true in
#check @ShielddSecurity.MerkleFieldFold196.field_root
#print axioms ShielddSecurity.MerkleFieldFold196.field_root
