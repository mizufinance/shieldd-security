import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0033
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L09B12
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 140).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4664)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7154 16
def localParent : Nat → Option Row
 | 7154 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 290),[(29892,1)]⟩
 | 7155 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 291),[(29893,1)]⟩
 | 7156 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 292),[(29895,1)]⟩
 | 7157 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 293),[(29894,4),(29895,1)]⟩
 | 7158 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 294),[(29896,1)]⟩
 | 7159 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 295),[(29897,1)]⟩
 | 7160 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 296),[(29899,1)]⟩
 | 7161 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 297),[(29898,4),(29899,1)]⟩
 | 7162 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 298),[(29900,1)]⟩
 | 7163 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 299),[(29901,1)]⟩
 | 7164 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 300),[(29903,1)]⟩
 | 7165 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 301),[(29902,4),(29903,1)]⟩
 | 7166 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 302),[(29904,1)]⟩
 | 7167 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 303),[(29905,1)]⟩
 | 7168 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 304),[(29907,1)]⟩
 | 7169 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 305),[(29906,4),(29907,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L09B12

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B12.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B12.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B12.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B12.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B12.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B12.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B12.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B12.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B12.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B12.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B12.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B12.count
