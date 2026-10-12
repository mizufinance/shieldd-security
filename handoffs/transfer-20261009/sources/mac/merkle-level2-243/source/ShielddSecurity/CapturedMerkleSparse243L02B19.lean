import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0020
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B19
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 252).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4298 16
def localParent : Nat → Option Row
 | 4298 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 20),[(27036,1)]⟩
 | 4299 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 21),[(27037,1)]⟩
 | 4300 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 22),[(27039,1)]⟩
 | 4301 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 23),[(27038,4),(27039,1)]⟩
 | 4302 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 24),[(27040,1)]⟩
 | 4303 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 25),[(27041,1)]⟩
 | 4304 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 26),[(27043,1)]⟩
 | 4305 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 27),[(27042,4),(27043,1)]⟩
 | 4306 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 28),[(27044,1)]⟩
 | 4307 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 29),[(27045,1)]⟩
 | 4308 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 30),[(27047,1)]⟩
 | 4309 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 31),[(27046,4),(27047,1)]⟩
 | 4310 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 32),[(27048,1)]⟩
 | 4311 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 33),[(27049,1)]⟩
 | 4312 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 34),[(27051,1)]⟩
 | 4313 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 35),[(27050,4),(27051,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B19

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B19.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B19.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B19.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B19.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B19.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B19.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B19.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B19.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B19.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B19.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B19.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B19.count
