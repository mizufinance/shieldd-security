import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0018
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleMiddle239Local
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 284).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1272)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3906 16
def localParent : Nat → Option Row
 | 3906 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 44),[(26644,1)]⟩
 | 3907 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 45),[(26645,1)]⟩
 | 3908 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 46),[(26647,1)]⟩
 | 3909 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 47),[(26646,4),(26647,1)]⟩
 | 3910 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 48),[(26648,1)]⟩
 | 3911 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 49),[(26649,1)]⟩
 | 3912 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 50),[(26651,1)]⟩
 | 3913 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 51),[(26650,4),(26651,1)]⟩
 | 3914 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 52),[(26652,1)]⟩
 | 3915 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 53),[(26653,1)]⟩
 | 3916 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 54),[(26655,1)]⟩
 | 3917 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 55),[(26654,4),(26655,1)]⟩
 | 3918 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 56),[(26656,1)]⟩
 | 3919 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 57),[(26657,1)]⟩
 | 3920 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 58),[(26659,1)]⟩
 | 3921 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 59),[(26658,4),(26659,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleMiddle239Local

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleMiddle239Local.rows
#print axioms ShielddSecurity.CapturedMerkleMiddle239Local.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleMiddle239Local.indices
#print axioms ShielddSecurity.CapturedMerkleMiddle239Local.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleMiddle239Local.localParent
#print axioms ShielddSecurity.CapturedMerkleMiddle239Local.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleMiddle239Local.localCheck
#print axioms ShielddSecurity.CapturedMerkleMiddle239Local.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleMiddle239Local.local_checked
#print axioms ShielddSecurity.CapturedMerkleMiddle239Local.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleMiddle239Local.count
#print axioms ShielddSecurity.CapturedMerkleMiddle239Local.count
