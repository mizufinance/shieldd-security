import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0037
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B22
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 300).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7738 16
def localParent : Nat → Option Row
 | 7738 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 42),[(30476,1)]⟩
 | 7739 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 43),[(30477,1)]⟩
 | 7740 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 44),[(30479,1)]⟩
 | 7741 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 45),[(30478,4),(30479,1)]⟩
 | 7742 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 46),[(30480,1)]⟩
 | 7743 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 47),[(30481,1)]⟩
 | 7744 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 48),[(30483,1)]⟩
 | 7745 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 49),[(30482,4),(30483,1)]⟩
 | 7746 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 50),[(30484,1)]⟩
 | 7747 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 51),[(30485,1)]⟩
 | 7748 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 52),[(30487,1)]⟩
 | 7749 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 53),[(30486,4),(30487,1)]⟩
 | 7750 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 54),[(30488,1)]⟩
 | 7751 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 55),[(30489,1)]⟩
 | 7752 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 56),[(30491,1)]⟩
 | 7753 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 57),[(30490,4),(30491,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B22

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B22.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B22.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B22.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B22.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B22.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B22.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B22.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B22.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B22.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B22.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B22.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B22.count
