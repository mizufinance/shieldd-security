import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0016
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L00B24
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 332).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 848)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3530 16
def localParent : Nat → Option Row
 | 3530 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 84),[(26268,1)]⟩
 | 3531 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 85),[(26269,1)]⟩
 | 3532 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 86),[(26271,1)]⟩
 | 3533 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 87),[(26270,4),(26271,1)]⟩
 | 3534 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 88),[(26272,1)]⟩
 | 3535 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 89),[(26273,1)]⟩
 | 3536 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 90),[(26275,1)]⟩
 | 3537 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 91),[(26274,4),(26275,1)]⟩
 | 3538 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 92),[(26276,1)]⟩
 | 3539 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 93),[(26277,1)]⟩
 | 3540 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 94),[(26279,1)]⟩
 | 3541 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 95),[(26278,4),(26279,1)]⟩
 | 3542 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 96),[(26280,1)]⟩
 | 3543 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 97),[(26281,1)]⟩
 | 3544 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 98),[(26283,1)]⟩
 | 3545 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 99),[(26282,4),(26283,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L00B24

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B24.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B24.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B24.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B24.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B24.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B24.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B24.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B24.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B24.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B24.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B24.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B24.count
