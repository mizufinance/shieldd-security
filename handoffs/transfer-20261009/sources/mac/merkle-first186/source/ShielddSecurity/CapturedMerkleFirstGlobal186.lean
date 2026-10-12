import ShielddSecurity.CapturedMerkleFirstGlobal186B00
import ShielddSecurity.CapturedMerkleFirstGlobal186B01
import ShielddSecurity.CapturedMerkleFirstGlobal186B02
import ShielddSecurity.CapturedMerkleFirstGlobal186B03
import ShielddSecurity.CapturedMerkleFirstGlobal186B04
import ShielddSecurity.CapturedMerkleFirstGlobal186B05
import ShielddSecurity.CapturedMerkleFirstGlobal186B06
import ShielddSecurity.CapturedMerkleFirstGlobal186B07
import ShielddSecurity.CapturedMerkleFirstGlobal186B08
import ShielddSecurity.CapturedMerkleFirstGlobal186B09
import ShielddSecurity.CapturedMerkleFirstGlobal186B10
import ShielddSecurity.CapturedMerkleFirstGlobal186B11
import ShielddSecurity.CapturedMerkleFirstGlobal186B12
import ShielddSecurity.CapturedMerkleFirstGlobal186B13
import ShielddSecurity.CapturedMerkleFirstGlobal186B14
import ShielddSecurity.CapturedMerkleFirstGlobal186B15
import ShielddSecurity.CapturedMerkleFirstGlobal186B16
import ShielddSecurity.CapturedMerkleFirstGlobal186B17
import ShielddSecurity.CapturedMerkleFirstGlobal186B18
import ShielddSecurity.CapturedMerkleFirstGlobal186B19
import ShielddSecurity.CapturedMerkleFirstGlobal186B20
import ShielddSecurity.CapturedMerkleFirstGlobal186B21
import ShielddSecurity.CapturedMerkleFirstGlobal186B22
import ShielddSecurity.CapturedMerkleFirstGlobal186B23
import ShielddSecurity.CapturedMerkleFirstGlobal186B24
import ShielddSecurity.CapturedMerkleFirstGlobal186B25
import ShielddSecurity.CompilerIndexedSlices183
import ShielddSecurity.CapturedMerkleFirstSelection186
import ShielddSecurity.CapturedRegistryGlobalSound176
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleFirstGlobal186
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172 CompilerIndexedSlices183
open CapturedInitial73419Generic01 (p copy)
def chunks : List (List Row) := slicesAt MerkleHash27Whole.selectedRows 0 [16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,12]
theorem partition : chunks.flatten=MerkleHash27Whole.selectedRows.take 412 := by
 rw [chunks,slicesAt_eq,List.drop_zero,slices_flatten]
 rfl
def copyCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 [200769] (MerkleHash27Whole.selectedRows.drop 412)
theorem copy_checked : copyCheck=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho (MerkleHash27Whole.selectedRows.take 412) := by
 rw [←partition]
 apply flatten_sound
 change AllSatisfied rho [CapturedMerkleFirstGlobal186B00.rows,CapturedMerkleFirstGlobal186B01.rows,CapturedMerkleFirstGlobal186B02.rows,CapturedMerkleFirstGlobal186B03.rows,CapturedMerkleFirstGlobal186B04.rows,CapturedMerkleFirstGlobal186B05.rows,CapturedMerkleFirstGlobal186B06.rows,CapturedMerkleFirstGlobal186B07.rows,CapturedMerkleFirstGlobal186B08.rows,CapturedMerkleFirstGlobal186B09.rows,CapturedMerkleFirstGlobal186B10.rows,CapturedMerkleFirstGlobal186B11.rows,CapturedMerkleFirstGlobal186B12.rows,CapturedMerkleFirstGlobal186B13.rows,CapturedMerkleFirstGlobal186B14.rows,CapturedMerkleFirstGlobal186B15.rows,CapturedMerkleFirstGlobal186B16.rows,CapturedMerkleFirstGlobal186B17.rows,CapturedMerkleFirstGlobal186B18.rows,CapturedMerkleFirstGlobal186B19.rows,CapturedMerkleFirstGlobal186B20.rows,CapturedMerkleFirstGlobal186B21.rows,CapturedMerkleFirstGlobal186B22.rows,CapturedMerkleFirstGlobal186B23.rows,CapturedMerkleFirstGlobal186B24.rows,CapturedMerkleFirstGlobal186B25.rows]
 exact ⟨CapturedMerkleFirstGlobal186B00.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B01.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B02.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B03.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B04.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B05.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B06.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B07.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B08.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B09.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B10.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B11.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B12.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B13.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B14.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B15.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B16.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B17.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B18.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B19.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B20.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B21.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B22.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B23.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B24.sound rho satisfied,⟨CapturedMerkleFirstGlobal186B25.sound rho satisfied,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho MerkleHash27Whole.selectedRows := by
 have copying := CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 [200769]
   (MerkleHash27Whole.selectedRows.drop 412) copy_checked rho
   ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
 intro row member
 rw [←List.take_append_drop 412 MerkleHash27Whole.selectedRows] at member
 rcases List.mem_append.mp member with member|member
 · exact arithmetic_sound rho satisfied row member
 · exact copying row member
theorem prior_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho MerkleHash27Whole.priorRows := by
 have families := CapturedRegistryGlobalSound176.row_families rho satisfied
 intro row member
 simp only [MerkleHash27Whole.priorRows,List.mem_append] at member
 rcases member with ((member|member)|member)|member
 · exact families.1 row member
 · exact families.2.1 row member
 · exact families.2.2 row member
 · exact CapturedMerkleFirstSelection186.sound rho satisfied row member
end ShielddSecurity.CapturedMerkleFirstGlobal186

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186.chunks
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186.chunks
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186.partition
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186.partition
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186.copyCheck
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186.copyCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186.copy_checked
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186.copy_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186.arithmetic_sound
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186.arithmetic_sound
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186.sound
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186.prior_sound
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186.prior_sound
