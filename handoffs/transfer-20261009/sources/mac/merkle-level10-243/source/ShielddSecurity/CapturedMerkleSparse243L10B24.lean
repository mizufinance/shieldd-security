import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0037
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B24
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 332).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7770 16
def localParent : Nat → Option Row
 | 7770 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 74),[(30508,1)]⟩
 | 7771 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 75),[(30509,1)]⟩
 | 7772 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 76),[(30511,1)]⟩
 | 7773 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 77),[(30510,4),(30511,1)]⟩
 | 7774 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 78),[(30512,1)]⟩
 | 7775 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 79),[(30513,1)]⟩
 | 7776 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 80),[(30515,1)]⟩
 | 7777 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 81),[(30514,4),(30515,1)]⟩
 | 7778 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 82),[(30516,1)]⟩
 | 7779 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 83),[(30517,1)]⟩
 | 7780 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 84),[(30519,1)]⟩
 | 7781 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 85),[(30518,4),(30519,1)]⟩
 | 7782 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 86),[(30520,1)]⟩
 | 7783 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 87),[(30521,1)]⟩
 | 7784 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 88),[(30523,1)]⟩
 | 7785 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 89),[(30522,4),(30523,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B24

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B24.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B24.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B24.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B24.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B24.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B24.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B24.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B24.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B24.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B24.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B24.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B24.count
