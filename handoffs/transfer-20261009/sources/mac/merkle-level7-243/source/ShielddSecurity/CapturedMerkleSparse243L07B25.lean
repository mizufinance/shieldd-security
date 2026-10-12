import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0031
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B25
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 348).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6514 16
def localParent : Nat → Option Row
 | 6514 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 66),[(29252,1)]⟩
 | 6515 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 67),[(29253,1)]⟩
 | 6516 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 68),[(29255,1)]⟩
 | 6517 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 69),[(29254,4),(29255,1)]⟩
 | 6518 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 70),[(29256,1)]⟩
 | 6519 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 71),[(29257,1)]⟩
 | 6520 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 72),[(29259,1)]⟩
 | 6521 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 73),[(29258,4),(29259,1)]⟩
 | 6522 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 74),[(29260,1)]⟩
 | 6523 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 75),[(29261,1)]⟩
 | 6524 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 76),[(29263,1)]⟩
 | 6525 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 77),[(29262,4),(29263,1)]⟩
 | 6526 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 78),[(29264,1)]⟩
 | 6527 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 79),[(29265,1)]⟩
 | 6528 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 80),[(29267,1)]⟩
 | 6529 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 81),[(29266,4),(29267,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B25

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B25.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B25.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B25.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B25.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B25.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B25.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B25.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B25.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B25.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B25.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B25.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B25.count
