import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0030
import ShielddSecurity.CapturedArithmetic45B0031
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B20
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 268).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6434 16
def localParent : Nat → Option Row
 | 6434 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 86),[(29172,1)]⟩
 | 6435 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 87),[(29173,1)]⟩
 | 6436 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 88),[(29175,1)]⟩
 | 6437 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 89),[(29174,4),(29175,1)]⟩
 | 6438 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 90),[(29176,1)]⟩
 | 6439 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 91),[(29177,1)]⟩
 | 6440 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 92),[(29179,1)]⟩
 | 6441 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 93),[(29178,4),(29179,1)]⟩
 | 6442 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 94),[(29180,1)]⟩
 | 6443 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 95),[(29181,1)]⟩
 | 6444 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 96),[(29183,1)]⟩
 | 6445 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 97),[(29182,4),(29183,1)]⟩
 | 6446 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 98),[(29184,1)]⟩
 | 6447 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 99),[(29185,1)]⟩
 | 6448 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 0),[(29187,1)]⟩
 | 6449 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 1),[(29186,4),(29187,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B20

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B20.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B20.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B20.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B20.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B20.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B20.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B20.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B20.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B20.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B20.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B20.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B20.count
