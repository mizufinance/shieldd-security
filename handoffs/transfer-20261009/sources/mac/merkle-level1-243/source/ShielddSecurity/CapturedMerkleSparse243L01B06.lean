import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0016
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L01B06
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 44).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1272)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3666 16
def localParent : Nat → Option Row
 | 3666 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 220),[(26404,1)]⟩
 | 3667 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 221),[(26405,1)]⟩
 | 3668 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 222),[(26407,1)]⟩
 | 3669 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 223),[(26406,4),(26407,1)]⟩
 | 3670 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 224),[(26408,1)]⟩
 | 3671 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 225),[(26409,1)]⟩
 | 3672 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 226),[(26411,1)]⟩
 | 3673 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 227),[(26410,4),(26411,1)]⟩
 | 3674 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 228),[(26412,1)]⟩
 | 3675 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 229),[(26413,1)]⟩
 | 3676 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 230),[(26415,1)]⟩
 | 3677 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 231),[(26414,4),(26415,1)]⟩
 | 3678 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 232),[(26416,1)]⟩
 | 3679 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 233),[(26417,1)]⟩
 | 3680 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 234),[(26419,1)]⟩
 | 3681 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 235),[(26418,4),(26419,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L01B06

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B06.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B06.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B06.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B06.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B06.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B06.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B06.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B06.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B06.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B06.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B06.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B06.count
