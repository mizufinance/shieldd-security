import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0028
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B19
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 252).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5994 16
def localParent : Nat → Option Row
 | 5994 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 58),[(28732,1)]⟩
 | 5995 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 59),[(28733,1)]⟩
 | 5996 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 60),[(28735,1)]⟩
 | 5997 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 61),[(28734,4),(28735,1)]⟩
 | 5998 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 62),[(28736,1)]⟩
 | 5999 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 63),[(28737,1)]⟩
 | 6000 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 64),[(28739,1)]⟩
 | 6001 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 65),[(28738,4),(28739,1)]⟩
 | 6002 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 66),[(28740,1)]⟩
 | 6003 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 67),[(28741,1)]⟩
 | 6004 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 68),[(28743,1)]⟩
 | 6005 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 69),[(28742,4),(28743,1)]⟩
 | 6006 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 70),[(28744,1)]⟩
 | 6007 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 71),[(28745,1)]⟩
 | 6008 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 72),[(28747,1)]⟩
 | 6009 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 73),[(28746,4),(28747,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B19

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B19.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B19.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B19.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B19.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B19.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B19.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B19.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B19.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B19.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B19.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B19.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B19.count
