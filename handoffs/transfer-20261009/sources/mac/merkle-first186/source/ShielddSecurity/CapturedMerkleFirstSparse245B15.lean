import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0013
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleFirstSparse245B15
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 200).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 424)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 2974 16
def localParent : Nat → Option Row
 | 2974 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 62),[(25712,1)]⟩
 | 2975 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 63),[(25713,1)]⟩
 | 2976 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 64),[(25715,1)]⟩
 | 2977 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 65),[(25714,4),(25715,1)]⟩
 | 2978 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 66),[(25716,1)]⟩
 | 2979 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 67),[(25717,1)]⟩
 | 2980 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 68),[(25719,1)]⟩
 | 2981 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 69),[(25718,4),(25719,1)]⟩
 | 2982 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 70),[(25720,1)]⟩
 | 2983 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 71),[(25721,1)]⟩
 | 2984 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 72),[(25723,1)]⟩
 | 2985 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 73),[(25722,4),(25723,1)]⟩
 | 2986 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 74),[(25724,1)]⟩
 | 2987 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 75),[(25725,1)]⟩
 | 2988 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 76),[(25727,1)]⟩
 | 2989 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 77),[(25726,4),(25727,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleFirstSparse245B15

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B15.rows
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B15.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B15.indices
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B15.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B15.localParent
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B15.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B15.localCheck
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B15.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B15.local_checked
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B15.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B15.count
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B15.count
