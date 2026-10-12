import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0028
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B16
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 204).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5946 16
def localParent : Nat → Option Row
 | 5946 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 10),[(28684,1)]⟩
 | 5947 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 11),[(28685,1)]⟩
 | 5948 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 12),[(28687,1)]⟩
 | 5949 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 13),[(28686,4),(28687,1)]⟩
 | 5950 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 14),[(28688,1)]⟩
 | 5951 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 15),[(28689,1)]⟩
 | 5952 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 16),[(28691,1)]⟩
 | 5953 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 17),[(28690,4),(28691,1)]⟩
 | 5954 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 18),[(28692,1)]⟩
 | 5955 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 19),[(28693,1)]⟩
 | 5956 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 20),[(28695,1)]⟩
 | 5957 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 21),[(28694,4),(28695,1)]⟩
 | 5958 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 22),[(28696,1)]⟩
 | 5959 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 23),[(28697,1)]⟩
 | 5960 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 24),[(28699,1)]⟩
 | 5961 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 25),[(28698,4),(28699,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B16

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B16.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B16.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B16.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B16.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B16.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B16.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B16.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B16.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B16.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B16.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B16.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B16.count
