import ShielddSecurity.MerkleFamily32Whole
import ShielddSecurity.CompilerIndexedCopyStream171
import ShielddSecurity.CapturedFullRelation58
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleGlobalBody181
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def selectionRows (i : Fin 15) : List Row := MerkleFamily32Selection.actualRows i
def phase0Rows (i : Fin 15) : List Row := (MerkleFamily32Tables.data0 i).rows
def phase1Rows (i : Fin 15) : List Row := (MerkleFamily32Tables.data1 i).rows
def tailRows (i : Fin 15) : List Row := CompilerColumnRenaming05.rows
  (CompilerWindowRenaming05.swap 25064 396 (MerkleFamily32Tables.offset i)) R22.rows
def bodyRows (i : Fin 15) : List Row := ((selectionRows i++phase0Rows i)++phase1Rows i)++tailRows i
def arithmeticRows (i : Fin 15) : List Row :=
  ((selectionRows i |>.take 12)++(phase0Rows i |>.take 16))++(phase1Rows i |>.take 24)++(tailRows i |>.take 372)
def copyRows (i : Fin 15) : List Row :=
  ((selectionRows i |>.drop 12)++(phase0Rows i |>.drop 16))++(phase1Rows i |>.drop 24)++(tailRows i |>.drop 372)
def copyCheck (i : Fin 15) : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770
  (List.replicate (copyRows i).length 200769) (copyRows i)
variable {F : Type} [Field F] [CharP F p]
theorem rows_exact (i : Fin 15) : MerkleFamily32Whole.rows (F:=F) i=bodyRows i := by
  change selectionRows i++((phase0Rows i++phase1Rows i)++tailRows i)=bodyRows i
  simp only [bodyRows,List.append_assoc]
omit [CharP F p] in
theorem body_sound (i : Fin 15) (rho : Nat → F)
    (arithmetic : Satisfies rho (arithmeticRows i)) (copying : Satisfies rho (copyRows i)) :
    Satisfies rho (bodyRows i) := by
  intro row member
  simp only [bodyRows,List.mem_append] at member
  rcases member with ((member|member)|member)|member
  · rw [←List.take_append_drop 12 (selectionRows i)] at member
    rcases List.mem_append.mp member with member|member
    · exact arithmetic row (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member)))
    · exact copying row (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member)))
  · rw [←List.take_append_drop 16 (phase0Rows i)] at member
    rcases List.mem_append.mp member with member|member
    · exact arithmetic row (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ member)))
    · exact copying row (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ member)))
  · rw [←List.take_append_drop 24 (phase1Rows i)] at member
    rcases List.mem_append.mp member with member|member
    · exact arithmetic row (List.mem_append_left _ (List.mem_append_right _ member))
    · exact copying row (List.mem_append_left _ (List.mem_append_right _ member))
  · rw [←List.take_append_drop 372 (tailRows i)] at member
    rcases List.mem_append.mp member with member|member
    · exact arithmetic row (List.mem_append_right _ member)
    · exact copying row (List.mem_append_right _ member)
theorem copy_sound (i : Fin 15) (checked : copyCheck i=true) (rho : Nat → F)
    (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : Satisfies rho (copyRows i) :=
  CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770
    (List.replicate (copyRows i).length 200769) (copyRows i) checked rho
    ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
theorem sound (i : Fin 15) (checked : copyCheck i=true) (rho : Nat → F)
    (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
    (arithmetic : Satisfies rho (arithmeticRows i)) : Satisfies rho (MerkleFamily32Whole.rows (F:=F) i) := by
  rw [rows_exact]
  exact body_sound i rho arithmetic (copy_sound i checked rho satisfied)
end ShielddSecurity.MerkleGlobalBody181

set_option pp.all true in
#check @ShielddSecurity.MerkleGlobalBody181.selectionRows
#print axioms ShielddSecurity.MerkleGlobalBody181.selectionRows
set_option pp.all true in
#check @ShielddSecurity.MerkleGlobalBody181.phase0Rows
#print axioms ShielddSecurity.MerkleGlobalBody181.phase0Rows
set_option pp.all true in
#check @ShielddSecurity.MerkleGlobalBody181.phase1Rows
#print axioms ShielddSecurity.MerkleGlobalBody181.phase1Rows
set_option pp.all true in
#check @ShielddSecurity.MerkleGlobalBody181.tailRows
#print axioms ShielddSecurity.MerkleGlobalBody181.tailRows
set_option pp.all true in
#check @ShielddSecurity.MerkleGlobalBody181.bodyRows
#print axioms ShielddSecurity.MerkleGlobalBody181.bodyRows
set_option pp.all true in
#check @ShielddSecurity.MerkleGlobalBody181.arithmeticRows
#print axioms ShielddSecurity.MerkleGlobalBody181.arithmeticRows
set_option pp.all true in
#check @ShielddSecurity.MerkleGlobalBody181.copyRows
#print axioms ShielddSecurity.MerkleGlobalBody181.copyRows
set_option pp.all true in
#check @ShielddSecurity.MerkleGlobalBody181.copyCheck
#print axioms ShielddSecurity.MerkleGlobalBody181.copyCheck
set_option pp.all true in
#check @ShielddSecurity.MerkleGlobalBody181.rows_exact
#print axioms ShielddSecurity.MerkleGlobalBody181.rows_exact
set_option pp.all true in
#check @ShielddSecurity.MerkleGlobalBody181.body_sound
#print axioms ShielddSecurity.MerkleGlobalBody181.body_sound
set_option pp.all true in
#check @ShielddSecurity.MerkleGlobalBody181.copy_sound
#print axioms ShielddSecurity.MerkleGlobalBody181.copy_sound
set_option pp.all true in
#check @ShielddSecurity.MerkleGlobalBody181.sound
#print axioms ShielddSecurity.MerkleGlobalBody181.sound
