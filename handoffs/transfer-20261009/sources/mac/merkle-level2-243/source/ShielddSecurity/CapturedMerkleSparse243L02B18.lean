import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0020
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B18
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 236).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4282 16
def localParent : Nat → Option Row
 | 4282 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 4),[(27020,1)]⟩
 | 4283 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 5),[(27021,1)]⟩
 | 4284 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 6),[(27023,1)]⟩
 | 4285 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 7),[(27022,4),(27023,1)]⟩
 | 4286 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 8),[(27024,1)]⟩
 | 4287 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 9),[(27025,1)]⟩
 | 4288 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 10),[(27027,1)]⟩
 | 4289 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 11),[(27026,4),(27027,1)]⟩
 | 4290 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 12),[(27028,1)]⟩
 | 4291 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 13),[(27029,1)]⟩
 | 4292 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 14),[(27031,1)]⟩
 | 4293 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 15),[(27030,4),(27031,1)]⟩
 | 4294 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 16),[(27032,1)]⟩
 | 4295 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 17),[(27033,1)]⟩
 | 4296 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 18),[(27035,1)]⟩
 | 4297 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 19),[(27034,4),(27035,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B18

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B18.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B18.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B18.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B18.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B18.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B18.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B18.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B18.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B18.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B18.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B18.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B18.count
