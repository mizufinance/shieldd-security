import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0015
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L00B12
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 140).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 848)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3338 16
def localParent : Nat → Option Row
 | 3338 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 18),[(26076,1)]⟩
 | 3339 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 19),[(26077,1)]⟩
 | 3340 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 20),[(26079,1)]⟩
 | 3341 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 21),[(26078,4),(26079,1)]⟩
 | 3342 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 22),[(26080,1)]⟩
 | 3343 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 23),[(26081,1)]⟩
 | 3344 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 24),[(26083,1)]⟩
 | 3345 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 25),[(26082,4),(26083,1)]⟩
 | 3346 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 26),[(26084,1)]⟩
 | 3347 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 27),[(26085,1)]⟩
 | 3348 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 28),[(26087,1)]⟩
 | 3349 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 29),[(26086,4),(26087,1)]⟩
 | 3350 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 30),[(26088,1)]⟩
 | 3351 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 31),[(26089,1)]⟩
 | 3352 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 32),[(26091,1)]⟩
 | 3353 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 33),[(26090,4),(26091,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L00B12

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B12.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B12.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B12.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B12.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B12.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B12.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B12.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B12.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B12.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B12.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B12.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B12.count
