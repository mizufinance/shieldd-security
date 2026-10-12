import ShielddSecurity.MerkleFamily32Tables
import ShielddSecurity.CapturedRegistryTail22
import ShielddSecurity.CapturedArithmetic45B0018
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleLocal233Certificate
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 268).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 (MerkleFamily32Tables.offset 1))
   (CompilerColumnRenaming05.row R22.ren row))
def indices : List Nat := List.range' 3890 16
def localParent : Nat → Option Row
 | 3890 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 28),[(26628,1)]⟩
 | 3891 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 29),[(26629,1)]⟩
 | 3892 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 30),[(26631,1)]⟩
 | 3893 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 31),[(26630,4),(26631,1)]⟩
 | 3894 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 32),[(26632,1)]⟩
 | 3895 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 33),[(26633,1)]⟩
 | 3896 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 34),[(26635,1)]⟩
 | 3897 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 35),[(26634,4),(26635,1)]⟩
 | 3898 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 36),[(26636,1)]⟩
 | 3899 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 37),[(26637,1)]⟩
 | 3900 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 38),[(26639,1)]⟩
 | 3901 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 39),[(26638,4),(26639,1)]⟩
 | 3902 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 40),[(26640,1)]⟩
 | 3903 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 41),[(26641,1)]⟩
 | 3904 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 42),[(26643,1)]⟩
 | 3905 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 43),[(26642,4),(26643,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleLocal233Certificate

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal233Certificate.rows
#print axioms ShielddSecurity.CapturedMerkleLocal233Certificate.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal233Certificate.indices
#print axioms ShielddSecurity.CapturedMerkleLocal233Certificate.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal233Certificate.localParent
#print axioms ShielddSecurity.CapturedMerkleLocal233Certificate.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal233Certificate.localCheck
#print axioms ShielddSecurity.CapturedMerkleLocal233Certificate.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal233Certificate.local_checked
#print axioms ShielddSecurity.CapturedMerkleLocal233Certificate.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal233Certificate.count
#print axioms ShielddSecurity.CapturedMerkleLocal233Certificate.count
