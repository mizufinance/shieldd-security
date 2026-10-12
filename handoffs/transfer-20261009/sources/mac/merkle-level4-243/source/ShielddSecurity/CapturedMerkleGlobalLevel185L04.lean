import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B00
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B01
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B02
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B03
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B04
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B05
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B06
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B07
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B08
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B09
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B10
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B11
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B12
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B13
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B14
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B15
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B16
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B17
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B18
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B19
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B20
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B21
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B22
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B23
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B24
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B25
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B26
import ShielddSecurity.CompilerIndexedSlices183
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleGlobalLevel185L04
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172 CompilerIndexedSlices183
open CapturedInitial73419Generic01 (p copy)
theorem arithmetic_count : (MerkleGlobalBody181.arithmeticRows 4).length=424 := by
 have selection := (MerkleFamily32Selection.counts 4).2
 have phase0 : (MerkleGlobalBody181.phase0Rows 4).length=17 := by rfl
 have phase1 : (MerkleGlobalBody181.phase1Rows 4).length=25 := by rfl
 have tail : (MerkleGlobalBody181.tailRows 4).length=373 := by
   simpa only [MerkleGlobalBody181.tailRows,CompilerColumnRenaming05.rows,List.length_map] using R22.counts.2.1
 simp only [MerkleGlobalBody181.arithmeticRows,MerkleGlobalBody181.selectionRows,List.length_append,List.length_take]
 rw [selection,phase0,phase1,tail]
 rfl
def chunks : List (List Row) := slicesAt (MerkleGlobalBody181.arithmeticRows 4) 0 [16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,8]
theorem partition : chunks.flatten=MerkleGlobalBody181.arithmeticRows 4 := by
 apply CompilerIndexedSlices183.partition
 rw [arithmetic_count]
 decide
theorem copy_checked : MerkleGlobalBody181.copyCheck 4=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho (MerkleGlobalBody181.arithmeticRows 4) := by
 rw [←partition]
 apply flatten_sound
 change AllSatisfied rho [CapturedMerkleGlobalArithmetic184L04B00.rows,CapturedMerkleGlobalArithmetic184L04B01.rows,CapturedMerkleGlobalArithmetic184L04B02.rows,CapturedMerkleGlobalArithmetic184L04B03.rows,CapturedMerkleGlobalArithmetic184L04B04.rows,CapturedMerkleGlobalArithmetic184L04B05.rows,CapturedMerkleGlobalArithmetic184L04B06.rows,CapturedMerkleGlobalArithmetic184L04B07.rows,CapturedMerkleGlobalArithmetic184L04B08.rows,CapturedMerkleGlobalArithmetic184L04B09.rows,CapturedMerkleGlobalArithmetic184L04B10.rows,CapturedMerkleGlobalArithmetic184L04B11.rows,CapturedMerkleGlobalArithmetic184L04B12.rows,CapturedMerkleGlobalArithmetic184L04B13.rows,CapturedMerkleGlobalArithmetic184L04B14.rows,CapturedMerkleGlobalArithmetic184L04B15.rows,CapturedMerkleGlobalArithmetic184L04B16.rows,CapturedMerkleGlobalArithmetic184L04B17.rows,CapturedMerkleGlobalArithmetic184L04B18.rows,CapturedMerkleGlobalArithmetic184L04B19.rows,CapturedMerkleGlobalArithmetic184L04B20.rows,CapturedMerkleGlobalArithmetic184L04B21.rows,CapturedMerkleGlobalArithmetic184L04B22.rows,CapturedMerkleGlobalArithmetic184L04B23.rows,CapturedMerkleGlobalArithmetic184L04B24.rows,CapturedMerkleGlobalArithmetic184L04B25.rows,CapturedMerkleGlobalArithmetic184L04B26.rows]
 exact ⟨CapturedMerkleGlobalArithmetic184L04B00.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B01.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B02.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B03.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B04.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B05.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B06.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B07.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B08.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B09.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B10.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B11.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B12.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B13.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B14.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B15.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B16.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B17.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B18.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B19.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B20.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B21.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B22.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B23.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B24.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B25.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L04B26.sound rho satisfied,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho (MerkleFamily32Whole.rows (F:=F) 4) :=
 MerkleGlobalBody181.sound 4 copy_checked rho satisfied (arithmetic_sound rho satisfied)
end ShielddSecurity.CapturedMerkleGlobalLevel185L04

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L04.arithmetic_count
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L04.arithmetic_count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L04.chunks
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L04.chunks
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L04.partition
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L04.partition
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L04.copy_checked
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L04.copy_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L04.arithmetic_sound
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L04.arithmetic_sound
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L04.sound
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L04.sound
