import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0028
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B18
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 236).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5978 16
def localParent : Nat → Option Row
 | 5978 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 42),[(28716,1)]⟩
 | 5979 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 43),[(28717,1)]⟩
 | 5980 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 44),[(28719,1)]⟩
 | 5981 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 45),[(28718,4),(28719,1)]⟩
 | 5982 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 46),[(28720,1)]⟩
 | 5983 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 47),[(28721,1)]⟩
 | 5984 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 48),[(28723,1)]⟩
 | 5985 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 49),[(28722,4),(28723,1)]⟩
 | 5986 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 50),[(28724,1)]⟩
 | 5987 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 51),[(28725,1)]⟩
 | 5988 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 52),[(28727,1)]⟩
 | 5989 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 53),[(28726,4),(28727,1)]⟩
 | 5990 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 54),[(28728,1)]⟩
 | 5991 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 55),[(28729,1)]⟩
 | 5992 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 56),[(28731,1)]⟩
 | 5993 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 57),[(28730,4),(28731,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B18

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B18.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B18.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B18.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B18.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B18.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B18.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B18.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B18.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B18.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B18.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B18.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B18.count
