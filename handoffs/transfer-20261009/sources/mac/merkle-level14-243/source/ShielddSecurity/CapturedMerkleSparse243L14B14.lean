import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0044
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B14
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 172).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9306 16
def localParent : Nat → Option Row
 | 9306 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 130),[(32044,1)]⟩
 | 9307 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 131),[(32045,1)]⟩
 | 9308 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 132),[(32047,1)]⟩
 | 9309 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 133),[(32046,4),(32047,1)]⟩
 | 9310 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 134),[(32048,1)]⟩
 | 9311 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 135),[(32049,1)]⟩
 | 9312 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 136),[(32051,1)]⟩
 | 9313 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 137),[(32050,4),(32051,1)]⟩
 | 9314 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 138),[(32052,1)]⟩
 | 9315 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 139),[(32053,1)]⟩
 | 9316 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 140),[(32055,1)]⟩
 | 9317 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 141),[(32054,4),(32055,1)]⟩
 | 9318 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 142),[(32056,1)]⟩
 | 9319 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 143),[(32057,1)]⟩
 | 9320 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 144),[(32059,1)]⟩
 | 9321 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 145),[(32058,4),(32059,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B14

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B14.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B14.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B14.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B14.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B14.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B14.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B14.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B14.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B14.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B14.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B14.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B14.count
