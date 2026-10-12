import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0037
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B25
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 348).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7786 16
def localParent : Nat → Option Row
 | 7786 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 90),[(30524,1)]⟩
 | 7787 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 91),[(30525,1)]⟩
 | 7788 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 92),[(30527,1)]⟩
 | 7789 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 93),[(30526,4),(30527,1)]⟩
 | 7790 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 94),[(30528,1)]⟩
 | 7791 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 95),[(30529,1)]⟩
 | 7792 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 96),[(30531,1)]⟩
 | 7793 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 97),[(30530,4),(30531,1)]⟩
 | 7794 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 98),[(30532,1)]⟩
 | 7795 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 99),[(30533,1)]⟩
 | 7796 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 100),[(30535,1)]⟩
 | 7797 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 101),[(30534,4),(30535,1)]⟩
 | 7798 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 102),[(30536,1)]⟩
 | 7799 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 103),[(30537,1)]⟩
 | 7800 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 104),[(30539,1)]⟩
 | 7801 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 105),[(30538,4),(30539,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B25

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B25.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B25.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B25.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B25.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B25.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B25.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B25.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B25.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B25.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B25.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B25.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B25.count
