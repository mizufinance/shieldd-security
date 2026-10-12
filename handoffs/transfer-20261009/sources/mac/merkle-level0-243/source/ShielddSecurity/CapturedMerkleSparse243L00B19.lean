import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0016
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L00B19
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 252).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 848)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3450 16
def localParent : Nat → Option Row
 | 3450 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 4),[(26188,1)]⟩
 | 3451 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 5),[(26189,1)]⟩
 | 3452 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 6),[(26191,1)]⟩
 | 3453 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 7),[(26190,4),(26191,1)]⟩
 | 3454 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 8),[(26192,1)]⟩
 | 3455 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 9),[(26193,1)]⟩
 | 3456 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 10),[(26195,1)]⟩
 | 3457 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 11),[(26194,4),(26195,1)]⟩
 | 3458 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 12),[(26196,1)]⟩
 | 3459 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 13),[(26197,1)]⟩
 | 3460 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 14),[(26199,1)]⟩
 | 3461 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 15),[(26198,4),(26199,1)]⟩
 | 3462 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 16),[(26200,1)]⟩
 | 3463 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 17),[(26201,1)]⟩
 | 3464 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 18),[(26203,1)]⟩
 | 3465 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 19),[(26202,4),(26203,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L00B19

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B19.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B19.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B19.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B19.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B19.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B19.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B19.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B19.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B19.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B19.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B19.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B19.count
