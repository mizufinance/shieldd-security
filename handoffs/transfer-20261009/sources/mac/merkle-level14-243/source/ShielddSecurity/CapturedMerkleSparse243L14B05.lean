import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0043
import ShielddSecurity.CapturedArithmetic45B0044
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B05
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 28).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9162 16
def localParent : Nat → Option Row
 | 9162 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 218),[(31900,1)]⟩
 | 9163 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 219),[(31901,1)]⟩
 | 9164 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 220),[(31903,1)]⟩
 | 9165 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 221),[(31902,4),(31903,1)]⟩
 | 9166 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 222),[(31904,1)]⟩
 | 9167 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 223),[(31905,1)]⟩
 | 9168 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 224),[(31907,1)]⟩
 | 9169 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 225),[(31906,4),(31907,1)]⟩
 | 9170 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 226),[(31908,1)]⟩
 | 9171 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 227),[(31909,1)]⟩
 | 9172 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 228),[(31911,1)]⟩
 | 9173 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 229),[(31910,4),(31911,1)]⟩
 | 9174 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 230),[(31912,1)]⟩
 | 9175 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 231),[(31913,1)]⟩
 | 9176 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 0),[(31915,1)]⟩
 | 9177 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 1),[(31914,4),(31915,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B05

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B05.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B05.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B05.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B05.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B05.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B05.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B05.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B05.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B05.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B05.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B05.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B05.count
