import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B00
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B01
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B02
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B03
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B04
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B05
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B06
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B07
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B08
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B09
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B10
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B11
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B12
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B13
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B14
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B15
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B16
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B17
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B18
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B19
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B20
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B21
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B22
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B23
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B24
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B25
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L06B26
import ShielddSecurity.CompilerIndexedSlices183
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleGlobalLevel185L06
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172 CompilerIndexedSlices183
open CapturedInitial73419Generic01 (p copy)
theorem arithmetic_count : (MerkleGlobalBody181.arithmeticRows 6).length=424 := by
 have selection := (MerkleFamily32Selection.counts 6).2
 have phase0 : (MerkleGlobalBody181.phase0Rows 6).length=17 := by rfl
 have phase1 : (MerkleGlobalBody181.phase1Rows 6).length=25 := by rfl
 have tail : (MerkleGlobalBody181.tailRows 6).length=373 := by
   simpa only [MerkleGlobalBody181.tailRows,CompilerColumnRenaming05.rows,List.length_map] using R22.counts.2.1
 simp only [MerkleGlobalBody181.arithmeticRows,MerkleGlobalBody181.selectionRows,List.length_append,List.length_take]
 rw [selection,phase0,phase1,tail]
 rfl
def chunks : List (List Row) := slicesAt (MerkleGlobalBody181.arithmeticRows 6) 0 [16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,8]
theorem partition : chunks.flatten=MerkleGlobalBody181.arithmeticRows 6 := by
 apply CompilerIndexedSlices183.partition
 rw [arithmetic_count]
 decide
theorem copy_checked : MerkleGlobalBody181.copyCheck 6=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho (MerkleGlobalBody181.arithmeticRows 6) := by
 rw [←partition]
 apply flatten_sound
 change AllSatisfied rho [CapturedMerkleGlobalArithmetic184L06B00.rows,CapturedMerkleGlobalArithmetic184L06B01.rows,CapturedMerkleGlobalArithmetic184L06B02.rows,CapturedMerkleGlobalArithmetic184L06B03.rows,CapturedMerkleGlobalArithmetic184L06B04.rows,CapturedMerkleGlobalArithmetic184L06B05.rows,CapturedMerkleGlobalArithmetic184L06B06.rows,CapturedMerkleGlobalArithmetic184L06B07.rows,CapturedMerkleGlobalArithmetic184L06B08.rows,CapturedMerkleGlobalArithmetic184L06B09.rows,CapturedMerkleGlobalArithmetic184L06B10.rows,CapturedMerkleGlobalArithmetic184L06B11.rows,CapturedMerkleGlobalArithmetic184L06B12.rows,CapturedMerkleGlobalArithmetic184L06B13.rows,CapturedMerkleGlobalArithmetic184L06B14.rows,CapturedMerkleGlobalArithmetic184L06B15.rows,CapturedMerkleGlobalArithmetic184L06B16.rows,CapturedMerkleGlobalArithmetic184L06B17.rows,CapturedMerkleGlobalArithmetic184L06B18.rows,CapturedMerkleGlobalArithmetic184L06B19.rows,CapturedMerkleGlobalArithmetic184L06B20.rows,CapturedMerkleGlobalArithmetic184L06B21.rows,CapturedMerkleGlobalArithmetic184L06B22.rows,CapturedMerkleGlobalArithmetic184L06B23.rows,CapturedMerkleGlobalArithmetic184L06B24.rows,CapturedMerkleGlobalArithmetic184L06B25.rows,CapturedMerkleGlobalArithmetic184L06B26.rows]
 exact ⟨CapturedMerkleGlobalArithmetic184L06B00.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B01.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B02.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B03.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B04.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B05.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B06.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B07.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B08.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B09.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B10.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B11.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B12.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B13.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B14.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B15.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B16.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B17.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B18.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B19.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B20.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B21.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B22.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B23.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B24.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B25.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L06B26.sound rho satisfied,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho (MerkleFamily32Whole.rows (F:=F) 6) :=
 MerkleGlobalBody181.sound 6 copy_checked rho satisfied (arithmetic_sound rho satisfied)
end ShielddSecurity.CapturedMerkleGlobalLevel185L06

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L06.arithmetic_count
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L06.arithmetic_count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L06.chunks
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L06.chunks
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L06.partition
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L06.partition
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L06.copy_checked
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L06.copy_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L06.arithmetic_sound
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L06.arithmetic_sound
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L06.sound
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L06.sound
