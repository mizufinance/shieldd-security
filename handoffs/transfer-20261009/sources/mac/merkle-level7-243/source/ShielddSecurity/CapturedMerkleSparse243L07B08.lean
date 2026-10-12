import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0029
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B08
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 76).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6242 16
def localParent : Nat → Option Row
 | 6242 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 212),[(28980,1)]⟩
 | 6243 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 213),[(28981,1)]⟩
 | 6244 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 214),[(28983,1)]⟩
 | 6245 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 215),[(28982,4),(28983,1)]⟩
 | 6246 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 216),[(28984,1)]⟩
 | 6247 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 217),[(28985,1)]⟩
 | 6248 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 218),[(28987,1)]⟩
 | 6249 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 219),[(28986,4),(28987,1)]⟩
 | 6250 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 220),[(28988,1)]⟩
 | 6251 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 221),[(28989,1)]⟩
 | 6252 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 222),[(28991,1)]⟩
 | 6253 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 223),[(28990,4),(28991,1)]⟩
 | 6254 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 224),[(28992,1)]⟩
 | 6255 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 225),[(28993,1)]⟩
 | 6256 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 226),[(28995,1)]⟩
 | 6257 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 227),[(28994,4),(28995,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B08

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B08.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B08.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B08.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B08.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B08.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B08.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B08.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B08.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B08.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B08.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B08.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B08.count
