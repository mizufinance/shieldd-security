import ShielddSecurity.CapturedMerkleGlobalPilot182
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B01
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B02
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B03
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B04
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B05
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B06
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B07
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B08
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B09
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B10
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B11
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B12
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B13
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B14
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B15
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B16
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B17
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B18
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B19
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B20
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B21
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B22
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B23
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B24
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B25
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L00B26
import ShielddSecurity.CompilerIndexedSlices183
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleGlobalLevel185L00
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172 CompilerIndexedSlices183
open CapturedInitial73419Generic01 (p copy)
theorem arithmetic_count : (MerkleGlobalBody181.arithmeticRows 0).length=424 := by
 have selection := (MerkleFamily32Selection.counts 0).2
 have phase0 : (MerkleGlobalBody181.phase0Rows 0).length=17 := by rfl
 have phase1 : (MerkleGlobalBody181.phase1Rows 0).length=25 := by rfl
 have tail : (MerkleGlobalBody181.tailRows 0).length=373 := by
   simpa only [MerkleGlobalBody181.tailRows,CompilerColumnRenaming05.rows,List.length_map] using R22.counts.2.1
 simp only [MerkleGlobalBody181.arithmeticRows,MerkleGlobalBody181.selectionRows,List.length_append,List.length_take]
 rw [selection,phase0,phase1,tail]
 rfl
def chunks : List (List Row) := slicesAt (MerkleGlobalBody181.arithmeticRows 0) 0 [16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,8]
theorem partition : chunks.flatten=MerkleGlobalBody181.arithmeticRows 0 := by
 apply CompilerIndexedSlices183.partition
 rw [arithmetic_count]
 decide
theorem copy_checked : MerkleGlobalBody181.copyCheck 0=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho (MerkleGlobalBody181.arithmeticRows 0) := by
 rw [←partition]
 apply flatten_sound
 change AllSatisfied rho [CapturedMerkleGlobalPilot182.rows,CapturedMerkleGlobalArithmetic184L00B01.rows,CapturedMerkleGlobalArithmetic184L00B02.rows,CapturedMerkleGlobalArithmetic184L00B03.rows,CapturedMerkleGlobalArithmetic184L00B04.rows,CapturedMerkleGlobalArithmetic184L00B05.rows,CapturedMerkleGlobalArithmetic184L00B06.rows,CapturedMerkleGlobalArithmetic184L00B07.rows,CapturedMerkleGlobalArithmetic184L00B08.rows,CapturedMerkleGlobalArithmetic184L00B09.rows,CapturedMerkleGlobalArithmetic184L00B10.rows,CapturedMerkleGlobalArithmetic184L00B11.rows,CapturedMerkleGlobalArithmetic184L00B12.rows,CapturedMerkleGlobalArithmetic184L00B13.rows,CapturedMerkleGlobalArithmetic184L00B14.rows,CapturedMerkleGlobalArithmetic184L00B15.rows,CapturedMerkleGlobalArithmetic184L00B16.rows,CapturedMerkleGlobalArithmetic184L00B17.rows,CapturedMerkleGlobalArithmetic184L00B18.rows,CapturedMerkleGlobalArithmetic184L00B19.rows,CapturedMerkleGlobalArithmetic184L00B20.rows,CapturedMerkleGlobalArithmetic184L00B21.rows,CapturedMerkleGlobalArithmetic184L00B22.rows,CapturedMerkleGlobalArithmetic184L00B23.rows,CapturedMerkleGlobalArithmetic184L00B24.rows,CapturedMerkleGlobalArithmetic184L00B25.rows,CapturedMerkleGlobalArithmetic184L00B26.rows]
 exact ⟨CapturedMerkleGlobalPilot182.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B01.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B02.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B03.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B04.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B05.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B06.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B07.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B08.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B09.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B10.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B11.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B12.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B13.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B14.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B15.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B16.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B17.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B18.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B19.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B20.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B21.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B22.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B23.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B24.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B25.sound rho satisfied,⟨CapturedMerkleGlobalArithmetic184L00B26.sound rho satisfied,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho (MerkleFamily32Whole.rows (F:=F) 0) :=
 MerkleGlobalBody181.sound 0 copy_checked rho satisfied (arithmetic_sound rho satisfied)
end ShielddSecurity.CapturedMerkleGlobalLevel185L00

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L00.arithmetic_count
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L00.arithmetic_count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L00.chunks
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L00.chunks
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L00.partition
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L00.partition
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L00.copy_checked
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L00.copy_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L00.arithmetic_sound
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L00.arithmetic_sound
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalLevel185L00.sound
#print axioms ShielddSecurity.CapturedMerkleGlobalLevel185L00.sound
