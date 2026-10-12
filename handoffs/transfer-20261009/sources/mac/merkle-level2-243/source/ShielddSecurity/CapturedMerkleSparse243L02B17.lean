import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0019
import ShielddSecurity.CapturedArithmetic45B0020
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B17
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 220).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4266 16
def localParent : Nat → Option Row
 | 4266 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 144),[(27004,1)]⟩
 | 4267 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 145),[(27005,1)]⟩
 | 4268 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 146),[(27007,1)]⟩
 | 4269 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 147),[(27006,4),(27007,1)]⟩
 | 4270 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 148),[(27008,1)]⟩
 | 4271 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 149),[(27009,1)]⟩
 | 4272 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 150),[(27011,1)]⟩
 | 4273 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 151),[(27010,4),(27011,1)]⟩
 | 4274 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 152),[(27012,1)]⟩
 | 4275 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 153),[(27013,1)]⟩
 | 4276 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 154),[(27015,1)]⟩
 | 4277 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 155),[(27014,4),(27015,1)]⟩
 | 4278 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 0),[(27016,1)]⟩
 | 4279 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 1),[(27017,1)]⟩
 | 4280 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 2),[(27019,1)]⟩
 | 4281 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 3),[(27018,4),(27019,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B17

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B17.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B17.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B17.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B17.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B17.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B17.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B17.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B17.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B17.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B17.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B17.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B17.count
