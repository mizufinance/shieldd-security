import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0016
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L00B26
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 364).take 8).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 848)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3562 8
def localParent : Nat → Option Row
 | 3562 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 116),[(26300,1)]⟩
 | 3563 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 117),[(26301,1)]⟩
 | 3564 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 118),[(26303,1)]⟩
 | 3565 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 119),[(26302,4),(26303,1)]⟩
 | 3566 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 120),[(26304,1)]⟩
 | 3567 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 121),[(26305,1)]⟩
 | 3568 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 122),[(26307,1)]⟩
 | 3569 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 123),[(26306,4),(26307,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=8 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L00B26

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B26.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B26.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B26.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B26.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B26.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B26.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B26.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B26.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B26.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B26.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B26.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B26.count
