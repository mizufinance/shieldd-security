import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0016
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L01B05
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 28).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1272)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3650 16
def localParent : Nat → Option Row
 | 3650 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 204),[(26388,1)]⟩
 | 3651 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 205),[(26389,1)]⟩
 | 3652 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 206),[(26391,1)]⟩
 | 3653 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 207),[(26390,4),(26391,1)]⟩
 | 3654 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 208),[(26392,1)]⟩
 | 3655 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 209),[(26393,1)]⟩
 | 3656 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 210),[(26395,1)]⟩
 | 3657 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 211),[(26394,4),(26395,1)]⟩
 | 3658 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 212),[(26396,1)]⟩
 | 3659 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 213),[(26397,1)]⟩
 | 3660 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 214),[(26399,1)]⟩
 | 3661 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 215),[(26398,4),(26399,1)]⟩
 | 3662 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 216),[(26400,1)]⟩
 | 3663 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 217),[(26401,1)]⟩
 | 3664 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 218),[(26403,1)]⟩
 | 3665 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 219),[(26402,4),(26403,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L01B05

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B05.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B05.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B05.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B05.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B05.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B05.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B05.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B05.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B05.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B05.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B05.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B05.count
