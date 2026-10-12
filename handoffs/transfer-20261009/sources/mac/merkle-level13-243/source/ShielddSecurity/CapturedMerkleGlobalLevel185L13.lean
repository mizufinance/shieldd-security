import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B00
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B01
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B02
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B03
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B04
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B05
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B06
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B07
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B08
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B09
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B10
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B11
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B12
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B13
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B14
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B15
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B16
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B17
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B18
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B19
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B20
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B21
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B22
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B23
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B24
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B25
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L13B26
import ShielddSecurity.CompilerIndexedSlices183
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleGlobalLevel185L13
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172 CompilerIndexedSlices183
open CapturedInitial73419Generic01 (p copy)
theorem arithmetic_count : (MerkleGlobalBody181.arithmeticRows 13).length=424 := by
 have selection := (MerkleFamily32Selection.counts 13).2
 have phase0 : (MerkleGlobalBody181.phase0Rows 13).length=17 := by rfl
 have phase1 : (MerkleGlobalBody181.phase1Rows 13).length=25 := by rfl
 have tail : (MerkleGlobalBody181.tailRows 13).length=373 := by
   simpa only [MerkleGlobalBody181.tailRows,CompilerColumnRenaming05.rows,List.length_map] using R22.counts.2.1
 simp only [MerkleGlobalBody181.arithmeticRows,MerkleGlobalBody181.selectionRows,List.length_append,List.length_take]
 rw [selection,phase0,phase1,tail]
 rfl
def chunks : List (List Row) := slicesAt (MerkleGlobalBody181.arithmeticRows 13) 0 [16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,8]
theorem partition : chunks.flatten=MerkleGlobalBody181.arithmeticRows 13 := by
 apply CompilerIndexedSlices183.partition
 rw [arithmetic_count]
 decide
theorem copy_checked : MerkleGlobalBody181.copyCheck 13=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho (MerkleGlobalBody181.arithmeticRows 13) := by
 rw [←partition]
 apply flatten_sound
 change AllSatisfied rho [CapturedMerkleGlobalArithmetic184L13B00.rows,CapturedMerkleGlobalArithmetic184L13B01.rows,CapturedMerkleGlobalArithmetic184L13B02.rows,CapturedMerkleGlobalArithmetic184L13B03.rows,CapturedMerkleGlobalArithmetic184L13B04.rows,CapturedMerkleGlobalArithmetic184L13B05.rows,CapturedMerkleGlobalArithmetic184L13B06.rows,CapturedMerkleGlobalArithmetic184L13B07.rows,CapturedMerkleGlobalArithmetic184L13B08.rows,CapturedMerkleGlobalArithmetic184L13B09.rows,CapturedMerkleGlobalArithmetic184L13B10.rows,CapturedMerkleGlobalArithmetic184L13B11.rows,CapturedMerkleGlobalArithmetic184L13B12.rows,CapturedMerkleGlobalArithmetic184L13B13.rows,CapturedMerkleGlobalArithmetic184L13B14.rows,CapturedMerkleGlobalArithmetic184L13B15.rows,CapturedMerkleGlobalArithmetic184L13B16.rows,CapturedMerkleGlobalArithmetic184L13B17.rows,CapturedMerkleGlobalArithmetic184L13B18.rows,CapturedMerkleGlobalArithmetic184L13B19.rows,CapturedMerkleGlobalArithmetic184L13B20.rows,CapturedMerkleGlobalArithmetic184L13B21.rows,CapturedMerkleGlobalArithmetic184L13B22.rows,CapturedMerkleGlobalArithmetic184L13B23.rows,CapturedMerkleGlobalArithmetic184L13B24.rows,CapturedMerkleGlobalArithmetic184L13B25.rows,CapturedMerkleGlobalArithmetic184L13B26.rows]
 exact ⟨CapturedMerkleGlobalArithmetic184L13B00.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B01.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B02.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B03.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B04.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B05.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B06.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B07.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B08.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B09.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B10.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B11.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B12.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B13.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B14.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B15.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B16.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B17.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B18.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B19.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B20.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B21.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B22.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B23.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B24.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B25.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L13B26.sound rho satisfied,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho (MerkleFamily32Whole.rows (F:=F) 13) :=
 MerkleGlobalBody181.sound 13 copy_checked rho satisfied (arithmetic_sound rho satisfied)
end ShielddSecurity.CapturedMerkleGlobalLevel185L13

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L13.arithmetic_count
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L13.arithmetic_count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L13.chunks
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L13.chunks
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L13.partition
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L13.partition
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L13.copy_checked
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L13.copy_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L13.arithmetic_sound
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L13.arithmetic_sound
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L13.sound
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L13.sound
