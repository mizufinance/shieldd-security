import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0025
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B12
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 140).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5458 16
def localParent : Nat → Option Row
 | 5458 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 238),[(28196,1)]⟩
 | 5459 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 239),[(28197,1)]⟩
 | 5460 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 240),[(28199,1)]⟩
 | 5461 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 241),[(28198,4),(28199,1)]⟩
 | 5462 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 242),[(28200,1)]⟩
 | 5463 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 243),[(28201,1)]⟩
 | 5464 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 244),[(28203,1)]⟩
 | 5465 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 245),[(28202,4),(28203,1)]⟩
 | 5466 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 246),[(28204,1)]⟩
 | 5467 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 247),[(28205,1)]⟩
 | 5468 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 248),[(28207,1)]⟩
 | 5469 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 249),[(28206,4),(28207,1)]⟩
 | 5470 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 250),[(28208,1)]⟩
 | 5471 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 251),[(28209,1)]⟩
 | 5472 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 252),[(28211,1)]⟩
 | 5473 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 253),[(28210,4),(28211,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B12

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B12.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B12.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B12.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B12.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B12.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B12.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B12.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B12.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B12.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B12.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B12.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B12.count
