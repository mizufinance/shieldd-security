import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0017
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L01B12
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 140).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1272)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3762 16
def localParent : Nat → Option Row
 | 3762 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 38),[(26500,1)]⟩
 | 3763 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 39),[(26501,1)]⟩
 | 3764 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 40),[(26503,1)]⟩
 | 3765 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 41),[(26502,4),(26503,1)]⟩
 | 3766 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 42),[(26504,1)]⟩
 | 3767 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 43),[(26505,1)]⟩
 | 3768 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 44),[(26507,1)]⟩
 | 3769 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 45),[(26506,4),(26507,1)]⟩
 | 3770 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 46),[(26508,1)]⟩
 | 3771 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 47),[(26509,1)]⟩
 | 3772 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 48),[(26511,1)]⟩
 | 3773 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 49),[(26510,4),(26511,1)]⟩
 | 3774 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 50),[(26512,1)]⟩
 | 3775 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 51),[(26513,1)]⟩
 | 3776 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 52),[(26515,1)]⟩
 | 3777 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 53),[(26514,4),(26515,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L01B12

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B12.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B12.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B12.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B12.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B12.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B12.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B12.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B12.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B12.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B12.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B12.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B12.count
