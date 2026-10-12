import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0013
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleFirstSparse245B17
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 232).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 424)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3006 16
def localParent : Nat → Option Row
 | 3006 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 94),[(25744,1)]⟩
 | 3007 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 95),[(25745,1)]⟩
 | 3008 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 96),[(25747,1)]⟩
 | 3009 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 97),[(25746,4),(25747,1)]⟩
 | 3010 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 98),[(25748,1)]⟩
 | 3011 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 99),[(25749,1)]⟩
 | 3012 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 100),[(25751,1)]⟩
 | 3013 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 101),[(25750,4),(25751,1)]⟩
 | 3014 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 102),[(25752,1)]⟩
 | 3015 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 103),[(25753,1)]⟩
 | 3016 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 104),[(25755,1)]⟩
 | 3017 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 105),[(25754,4),(25755,1)]⟩
 | 3018 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 106),[(25756,1)]⟩
 | 3019 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 107),[(25757,1)]⟩
 | 3020 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 108),[(25759,1)]⟩
 | 3021 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 109),[(25758,4),(25759,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleFirstSparse245B17

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B17.rows
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B17.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B17.indices
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B17.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B17.localParent
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B17.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B17.localCheck
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B17.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B17.local_checked
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B17.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B17.count
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B17.count
