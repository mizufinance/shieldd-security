import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0016
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L00B23
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 316).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 848)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3514 16
def localParent : Nat → Option Row
 | 3514 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 68),[(26252,1)]⟩
 | 3515 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 69),[(26253,1)]⟩
 | 3516 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 70),[(26255,1)]⟩
 | 3517 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 71),[(26254,4),(26255,1)]⟩
 | 3518 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 72),[(26256,1)]⟩
 | 3519 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 73),[(26257,1)]⟩
 | 3520 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 74),[(26259,1)]⟩
 | 3521 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 75),[(26258,4),(26259,1)]⟩
 | 3522 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 76),[(26260,1)]⟩
 | 3523 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 77),[(26261,1)]⟩
 | 3524 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 78),[(26263,1)]⟩
 | 3525 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 79),[(26262,4),(26263,1)]⟩
 | 3526 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 80),[(26264,1)]⟩
 | 3527 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 81),[(26265,1)]⟩
 | 3528 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 82),[(26267,1)]⟩
 | 3529 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 83),[(26266,4),(26267,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L00B23

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B23.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B23.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B23.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B23.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B23.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B23.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B23.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B23.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B23.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B23.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B23.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B23.count
