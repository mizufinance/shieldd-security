import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B00
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B01
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B02
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B03
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B04
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B05
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B06
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B07
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B08
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B09
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B10
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B11
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B12
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B13
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B14
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B15
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B16
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B17
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B18
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B19
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B20
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B21
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B22
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B23
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B24
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B25
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L02B26
import ShielddSecurity.CompilerIndexedSlices183
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleGlobalLevel185L02
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172 CompilerIndexedSlices183
open CapturedInitial73419Generic01 (p copy)
theorem arithmetic_count : (MerkleGlobalBody181.arithmeticRows 2).length=424 := by
 have selection := (MerkleFamily32Selection.counts 2).2
 have phase0 : (MerkleGlobalBody181.phase0Rows 2).length=17 := by rfl
 have phase1 : (MerkleGlobalBody181.phase1Rows 2).length=25 := by rfl
 have tail : (MerkleGlobalBody181.tailRows 2).length=373 := by
   simpa only [MerkleGlobalBody181.tailRows,CompilerColumnRenaming05.rows,List.length_map] using R22.counts.2.1
 simp only [MerkleGlobalBody181.arithmeticRows,MerkleGlobalBody181.selectionRows,List.length_append,List.length_take]
 rw [selection,phase0,phase1,tail]
 rfl
def chunks : List (List Row) := slicesAt (MerkleGlobalBody181.arithmeticRows 2) 0 [16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,8]
theorem partition : chunks.flatten=MerkleGlobalBody181.arithmeticRows 2 := by
 apply CompilerIndexedSlices183.partition
 rw [arithmetic_count]
 decide
theorem copy_checked : MerkleGlobalBody181.copyCheck 2=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho (MerkleGlobalBody181.arithmeticRows 2) := by
 rw [←partition]
 apply flatten_sound
 change AllSatisfied rho [CapturedMerkleGlobalArithmetic184L02B00.rows,CapturedMerkleGlobalArithmetic184L02B01.rows,CapturedMerkleGlobalArithmetic184L02B02.rows,CapturedMerkleGlobalArithmetic184L02B03.rows,CapturedMerkleGlobalArithmetic184L02B04.rows,CapturedMerkleGlobalArithmetic184L02B05.rows,CapturedMerkleGlobalArithmetic184L02B06.rows,CapturedMerkleGlobalArithmetic184L02B07.rows,CapturedMerkleGlobalArithmetic184L02B08.rows,CapturedMerkleGlobalArithmetic184L02B09.rows,CapturedMerkleGlobalArithmetic184L02B10.rows,CapturedMerkleGlobalArithmetic184L02B11.rows,CapturedMerkleGlobalArithmetic184L02B12.rows,CapturedMerkleGlobalArithmetic184L02B13.rows,CapturedMerkleGlobalArithmetic184L02B14.rows,CapturedMerkleGlobalArithmetic184L02B15.rows,CapturedMerkleGlobalArithmetic184L02B16.rows,CapturedMerkleGlobalArithmetic184L02B17.rows,CapturedMerkleGlobalArithmetic184L02B18.rows,CapturedMerkleGlobalArithmetic184L02B19.rows,CapturedMerkleGlobalArithmetic184L02B20.rows,CapturedMerkleGlobalArithmetic184L02B21.rows,CapturedMerkleGlobalArithmetic184L02B22.rows,CapturedMerkleGlobalArithmetic184L02B23.rows,CapturedMerkleGlobalArithmetic184L02B24.rows,CapturedMerkleGlobalArithmetic184L02B25.rows,CapturedMerkleGlobalArithmetic184L02B26.rows]
 exact ⟨CapturedMerkleGlobalArithmetic184L02B00.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B01.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B02.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B03.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B04.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B05.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B06.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B07.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B08.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B09.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B10.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B11.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B12.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B13.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B14.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B15.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B16.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B17.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B18.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B19.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B20.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B21.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B22.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B23.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B24.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B25.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L02B26.sound rho satisfied,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho (MerkleFamily32Whole.rows (F:=F) 2) :=
 MerkleGlobalBody181.sound 2 copy_checked rho satisfied (arithmetic_sound rho satisfied)
end ShielddSecurity.CapturedMerkleGlobalLevel185L02

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L02.arithmetic_count
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L02.arithmetic_count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L02.chunks
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L02.chunks
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L02.partition
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L02.partition
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L02.copy_checked
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L02.copy_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L02.arithmetic_sound
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L02.arithmetic_sound
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L02.sound
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L02.sound
