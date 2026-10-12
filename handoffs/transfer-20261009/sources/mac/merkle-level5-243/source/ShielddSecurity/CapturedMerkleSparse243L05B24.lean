import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0027
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B24
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 332).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5650 16
def localParent : Nat → Option Row
 | 5650 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 36),[(28388,1)]⟩
 | 5651 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 37),[(28389,1)]⟩
 | 5652 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 38),[(28391,1)]⟩
 | 5653 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 39),[(28390,4),(28391,1)]⟩
 | 5654 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 40),[(28392,1)]⟩
 | 5655 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 41),[(28393,1)]⟩
 | 5656 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 42),[(28395,1)]⟩
 | 5657 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 43),[(28394,4),(28395,1)]⟩
 | 5658 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 44),[(28396,1)]⟩
 | 5659 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 45),[(28397,1)]⟩
 | 5660 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 46),[(28399,1)]⟩
 | 5661 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 47),[(28398,4),(28399,1)]⟩
 | 5662 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 48),[(28400,1)]⟩
 | 5663 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 49),[(28401,1)]⟩
 | 5664 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 50),[(28403,1)]⟩
 | 5665 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 51),[(28402,4),(28403,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B24

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B24.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B24.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B24.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B24.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B24.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B24.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B24.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B24.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B24.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B24.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B24.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B24.count
