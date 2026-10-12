import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0020
import ShielddSecurity.CapturedArithmetic45B0021
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B05
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 28).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4498 16
def localParent : Nat → Option Row
 | 4498 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 220),[(27236,1)]⟩
 | 4499 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 221),[(27237,1)]⟩
 | 4500 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 222),[(27239,1)]⟩
 | 4501 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 223),[(27238,4),(27239,1)]⟩
 | 4502 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 0),[(27240,1)]⟩
 | 4503 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 1),[(27241,1)]⟩
 | 4504 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 2),[(27243,1)]⟩
 | 4505 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 3),[(27242,4),(27243,1)]⟩
 | 4506 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 4),[(27244,1)]⟩
 | 4507 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 5),[(27245,1)]⟩
 | 4508 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 6),[(27247,1)]⟩
 | 4509 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 7),[(27246,4),(27247,1)]⟩
 | 4510 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 8),[(27248,1)]⟩
 | 4511 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 9),[(27249,1)]⟩
 | 4512 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 10),[(27251,1)]⟩
 | 4513 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 11),[(27250,4),(27251,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B05

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B05.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B05.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B05.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B05.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B05.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B05.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B05.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B05.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B05.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B05.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B05.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B05.count
