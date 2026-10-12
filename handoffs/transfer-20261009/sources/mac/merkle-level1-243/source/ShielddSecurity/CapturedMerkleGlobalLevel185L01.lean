import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B00
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B01
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B02
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B03
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B04
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B05
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B06
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B07
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B08
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B09
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B10
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B11
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B12
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B13
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B14
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B15
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B16
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B17
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B18
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B19
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B20
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B21
import ShielddSecurity.CapturedMerkleWide223Pilot
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B24
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B25
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B26
import ShielddSecurity.CompilerIndexedSlices183
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleGlobalLevel185L01
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172 CompilerIndexedSlices183
open CapturedInitial73419Generic01 (p copy)
theorem arithmetic_count : (MerkleGlobalBody181.arithmeticRows 1).length=424 := by
 have selection := (MerkleFamily32Selection.counts 1).2
 have phase0 : (MerkleGlobalBody181.phase0Rows 1).length=17 := by rfl
 have phase1 : (MerkleGlobalBody181.phase1Rows 1).length=25 := by rfl
 have tail : (MerkleGlobalBody181.tailRows 1).length=373 := by
   simpa only [MerkleGlobalBody181.tailRows,CompilerColumnRenaming05.rows,List.length_map] using R22.counts.2.1
 simp only [MerkleGlobalBody181.arithmeticRows,MerkleGlobalBody181.selectionRows,List.length_append,List.length_take]
 rw [selection,phase0,phase1,tail]
 rfl
def chunks : List (List Row) := slicesAt (MerkleGlobalBody181.arithmeticRows 1) 0 [16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,32,16,16,8]
theorem partition : chunks.flatten=MerkleGlobalBody181.arithmeticRows 1 := by
 apply CompilerIndexedSlices183.partition
 rw [arithmetic_count]
 decide
theorem copy_checked : MerkleGlobalBody181.copyCheck 1=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho (MerkleGlobalBody181.arithmeticRows 1) := by
 rw [←partition]
 apply flatten_sound
 change AllSatisfied rho [CapturedMerkleGlobalArithmetic184L01B00.rows,CapturedMerkleGlobalArithmetic184L01B01.rows,CapturedMerkleGlobalArithmetic184L01B02.rows,CapturedMerkleGlobalArithmetic184L01B03.rows,CapturedMerkleGlobalArithmetic184L01B04.rows,CapturedMerkleGlobalArithmetic184L01B05.rows,CapturedMerkleGlobalArithmetic184L01B06.rows,CapturedMerkleGlobalArithmetic184L01B07.rows,CapturedMerkleGlobalArithmetic184L01B08.rows,CapturedMerkleGlobalArithmetic184L01B09.rows,CapturedMerkleGlobalArithmetic184L01B10.rows,CapturedMerkleGlobalArithmetic184L01B11.rows,CapturedMerkleGlobalArithmetic184L01B12.rows,CapturedMerkleGlobalArithmetic184L01B13.rows,CapturedMerkleGlobalArithmetic184L01B14.rows,CapturedMerkleGlobalArithmetic184L01B15.rows,CapturedMerkleGlobalArithmetic184L01B16.rows,CapturedMerkleGlobalArithmetic184L01B17.rows,CapturedMerkleGlobalArithmetic184L01B18.rows,CapturedMerkleGlobalArithmetic184L01B19.rows,CapturedMerkleGlobalArithmetic184L01B20.rows,CapturedMerkleGlobalArithmetic184L01B21.rows,CapturedMerkleWide223Pilot.rows,CapturedMerkleGlobalArithmetic184L01B24.rows,CapturedMerkleGlobalArithmetic184L01B25.rows,CapturedMerkleGlobalArithmetic184L01B26.rows]
 exact ⟨CapturedMerkleGlobalArithmetic184L01B00.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B01.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B02.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B03.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B04.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B05.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B06.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B07.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B08.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B09.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B10.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B11.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B12.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B13.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B14.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B15.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B16.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B17.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B18.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B19.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B20.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B21.sound rho satisfied,⟨CapturedMerkleWide223Pilot.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B24.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B25.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L01B26.sound rho satisfied,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho (MerkleFamily32Whole.rows (F:=F) 1) :=
 MerkleGlobalBody181.sound 1 copy_checked rho satisfied (arithmetic_sound rho satisfied)
end ShielddSecurity.CapturedMerkleGlobalLevel185L01

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L01.arithmetic_count
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L01.arithmetic_count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L01.chunks
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L01.chunks
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L01.partition
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L01.partition
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L01.copy_checked
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L01.copy_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L01.arithmetic_sound
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L01.arithmetic_sound
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L01.sound
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L01.sound
