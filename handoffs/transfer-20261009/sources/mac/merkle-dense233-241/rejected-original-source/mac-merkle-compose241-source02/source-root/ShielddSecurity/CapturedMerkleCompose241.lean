import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B20
import ShielddSecurity.CapturedMerkleGlobalArithmetic184L01B21
import ShielddSecurity.CapturedMerkleWide223Pilot
import ShielddSecurity.CompilerIndexedCopyChunks232
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleCompose241
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def rows : List Row := (MerkleGlobalBody181.arithmeticRows 1).drop 320 |>.take 64
def indices : List Nat := List.range' 3890 64
theorem rows_partition : rows=CapturedMerkleGlobalArithmetic184L01B20.rows++(CapturedMerkleGlobalArithmetic184L01B21.rows++CapturedMerkleWide223Pilot.rows) := by rfl
theorem indices_partition : indices=CapturedMerkleGlobalArithmetic184L01B20.indices++(CapturedMerkleGlobalArithmetic184L01B21.indices++CapturedMerkleWide223Pilot.indices) := by rfl
def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by
 have a : CapturedMerkleGlobalArithmetic184L01B20.indices.length=CapturedMerkleGlobalArithmetic184L01B20.rows.length := by
  rw [CapturedMerkleGlobalArithmetic184L01B20.count]
  rfl
 have b : CapturedMerkleGlobalArithmetic184L01B21.indices.length=CapturedMerkleGlobalArithmetic184L01B21.rows.length := by
  rw [CapturedMerkleGlobalArithmetic184L01B21.count]
  rfl
 change CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows=true
 rw [indices_partition,rows_partition]
 rw [CompilerIndexedCopyChunks232.check_append p copy CapturedFullRelation58.rowAt 200770
  CapturedMerkleGlobalArithmetic184L01B20.indices (CapturedMerkleGlobalArithmetic184L01B21.indices++CapturedMerkleWide223Pilot.indices) CapturedMerkleGlobalArithmetic184L01B20.rows (CapturedMerkleGlobalArithmetic184L01B21.rows++CapturedMerkleWide223Pilot.rows) a]
 rw [CompilerIndexedCopyChunks232.check_append p copy CapturedFullRelation58.rowAt 200770
  CapturedMerkleGlobalArithmetic184L01B21.indices CapturedMerkleWide223Pilot.indices CapturedMerkleGlobalArithmetic184L01B21.rows CapturedMerkleWide223Pilot.rows b]
 change (CapturedMerkleGlobalArithmetic184L01B20.productionCheck && (CapturedMerkleGlobalArithmetic184L01B21.productionCheck && CapturedMerkleWide223Pilot.productionCheck))=true
 rw [CapturedMerkleGlobalArithmetic184L01B20.checked,CapturedMerkleGlobalArithmetic184L01B21.checked,CapturedMerkleWide223Pilot.checked]
theorem count : rows.length=64 := by
 rw [rows_partition,List.length_append,List.length_append,CapturedMerkleGlobalArithmetic184L01B20.count,CapturedMerkleGlobalArithmetic184L01B21.count,CapturedMerkleWide223Pilot.count]
 rfl
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : Satisfies rho rows :=
 CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
  ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedMerkleCompose241

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleCompose241.rows
#print axioms ShielddSecurity.CapturedMerkleCompose241.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleCompose241.indices
#print axioms ShielddSecurity.CapturedMerkleCompose241.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleCompose241.rows_partition
#print axioms ShielddSecurity.CapturedMerkleCompose241.rows_partition
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleCompose241.indices_partition
#print axioms ShielddSecurity.CapturedMerkleCompose241.indices_partition
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleCompose241.productionCheck
#print axioms ShielddSecurity.CapturedMerkleCompose241.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleCompose241.checked
#print axioms ShielddSecurity.CapturedMerkleCompose241.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleCompose241.count
#print axioms ShielddSecurity.CapturedMerkleCompose241.count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleCompose241.sound
#print axioms ShielddSecurity.CapturedMerkleCompose241.sound
