import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0028
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B17
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 220).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5962 16
def localParent : Nat → Option Row
 | 5962 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 26),[(28700,1)]⟩
 | 5963 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 27),[(28701,1)]⟩
 | 5964 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 28),[(28703,1)]⟩
 | 5965 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 29),[(28702,4),(28703,1)]⟩
 | 5966 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 30),[(28704,1)]⟩
 | 5967 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 31),[(28705,1)]⟩
 | 5968 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 32),[(28707,1)]⟩
 | 5969 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 33),[(28706,4),(28707,1)]⟩
 | 5970 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 34),[(28708,1)]⟩
 | 5971 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 35),[(28709,1)]⟩
 | 5972 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 36),[(28711,1)]⟩
 | 5973 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 37),[(28710,4),(28711,1)]⟩
 | 5974 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 38),[(28712,1)]⟩
 | 5975 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 39),[(28713,1)]⟩
 | 5976 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 40),[(28715,1)]⟩
 | 5977 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 41),[(28714,4),(28715,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B17

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B17.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B17.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B17.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B17.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B17.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B17.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B17.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B17.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B17.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B17.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B17.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B17.count
