import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0039
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L11B22
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 300).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5512)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8162 16
def localParent : Nat → Option Row
 | 8162 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 50),[(30900,1)]⟩
 | 8163 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 51),[(30901,1)]⟩
 | 8164 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 52),[(30903,1)]⟩
 | 8165 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 53),[(30902,4),(30903,1)]⟩
 | 8166 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 54),[(30904,1)]⟩
 | 8167 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 55),[(30905,1)]⟩
 | 8168 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 56),[(30907,1)]⟩
 | 8169 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 57),[(30906,4),(30907,1)]⟩
 | 8170 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 58),[(30908,1)]⟩
 | 8171 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 59),[(30909,1)]⟩
 | 8172 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 60),[(30911,1)]⟩
 | 8173 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 61),[(30910,4),(30911,1)]⟩
 | 8174 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 62),[(30912,1)]⟩
 | 8175 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 63),[(30913,1)]⟩
 | 8176 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 64),[(30915,1)]⟩
 | 8177 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 65),[(30914,4),(30915,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L11B22

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B22.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B22.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B22.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B22.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B22.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B22.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B22.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B22.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B22.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B22.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B22.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B22.count
