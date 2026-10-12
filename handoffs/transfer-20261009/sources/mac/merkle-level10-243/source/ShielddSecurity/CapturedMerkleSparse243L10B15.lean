import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0036
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B15
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 188).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7626 16
def localParent : Nat → Option Row
 | 7626 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 46),[(30364,1)]⟩
 | 7627 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 47),[(30365,1)]⟩
 | 7628 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 48),[(30367,1)]⟩
 | 7629 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 49),[(30366,4),(30367,1)]⟩
 | 7630 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 50),[(30368,1)]⟩
 | 7631 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 51),[(30369,1)]⟩
 | 7632 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 52),[(30371,1)]⟩
 | 7633 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 53),[(30370,4),(30371,1)]⟩
 | 7634 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 54),[(30372,1)]⟩
 | 7635 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 55),[(30373,1)]⟩
 | 7636 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 56),[(30375,1)]⟩
 | 7637 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 57),[(30374,4),(30375,1)]⟩
 | 7638 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 58),[(30376,1)]⟩
 | 7639 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 59),[(30377,1)]⟩
 | 7640 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 60),[(30379,1)]⟩
 | 7641 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 61),[(30378,4),(30379,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B15

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B15.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B15.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B15.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B15.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B15.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B15.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B15.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B15.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B15.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B15.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B15.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B15.count
