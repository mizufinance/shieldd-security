import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0021
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B13
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 156).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4626 16
def localParent : Nat → Option Row
 | 4626 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 124),[(27364,1)]⟩
 | 4627 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 125),[(27365,1)]⟩
 | 4628 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 126),[(27367,1)]⟩
 | 4629 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 127),[(27366,4),(27367,1)]⟩
 | 4630 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 128),[(27368,1)]⟩
 | 4631 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 129),[(27369,1)]⟩
 | 4632 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 130),[(27371,1)]⟩
 | 4633 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 131),[(27370,4),(27371,1)]⟩
 | 4634 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 132),[(27372,1)]⟩
 | 4635 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 133),[(27373,1)]⟩
 | 4636 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 134),[(27375,1)]⟩
 | 4637 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 135),[(27374,4),(27375,1)]⟩
 | 4638 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 136),[(27376,1)]⟩
 | 4639 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 137),[(27377,1)]⟩
 | 4640 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 138),[(27379,1)]⟩
 | 4641 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 139),[(27378,4),(27379,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B13

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B13.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B13.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B13.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B13.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B13.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B13.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B13.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B13.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B13.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B13.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B13.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B13.count
