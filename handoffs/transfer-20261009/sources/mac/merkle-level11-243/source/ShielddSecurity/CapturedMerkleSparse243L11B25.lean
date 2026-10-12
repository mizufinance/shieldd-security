import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0039
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L11B25
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 348).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5512)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8210 16
def localParent : Nat → Option Row
 | 8210 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 98),[(30948,1)]⟩
 | 8211 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 99),[(30949,1)]⟩
 | 8212 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 100),[(30951,1)]⟩
 | 8213 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 101),[(30950,4),(30951,1)]⟩
 | 8214 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 102),[(30952,1)]⟩
 | 8215 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 103),[(30953,1)]⟩
 | 8216 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 104),[(30955,1)]⟩
 | 8217 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 105),[(30954,4),(30955,1)]⟩
 | 8218 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 106),[(30956,1)]⟩
 | 8219 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 107),[(30957,1)]⟩
 | 8220 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 108),[(30959,1)]⟩
 | 8221 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 109),[(30958,4),(30959,1)]⟩
 | 8222 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 110),[(30960,1)]⟩
 | 8223 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 111),[(30961,1)]⟩
 | 8224 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 112),[(30963,1)]⟩
 | 8225 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 113),[(30962,4),(30963,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L11B25

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B25.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B25.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B25.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B25.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B25.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B25.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B25.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B25.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B25.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B25.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B25.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B25.count
