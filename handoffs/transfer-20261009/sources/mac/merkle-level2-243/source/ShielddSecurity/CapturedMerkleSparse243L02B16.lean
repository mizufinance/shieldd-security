import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0019
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B16
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 204).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4250 16
def localParent : Nat → Option Row
 | 4250 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 128),[(26988,1)]⟩
 | 4251 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 129),[(26989,1)]⟩
 | 4252 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 130),[(26991,1)]⟩
 | 4253 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 131),[(26990,4),(26991,1)]⟩
 | 4254 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 132),[(26992,1)]⟩
 | 4255 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 133),[(26993,1)]⟩
 | 4256 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 134),[(26995,1)]⟩
 | 4257 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 135),[(26994,4),(26995,1)]⟩
 | 4258 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 136),[(26996,1)]⟩
 | 4259 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 137),[(26997,1)]⟩
 | 4260 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 138),[(26999,1)]⟩
 | 4261 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 139),[(26998,4),(26999,1)]⟩
 | 4262 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 140),[(27000,1)]⟩
 | 4263 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 141),[(27001,1)]⟩
 | 4264 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 142),[(27003,1)]⟩
 | 4265 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 143),[(27002,4),(27003,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B16

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B16.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B16.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B16.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B16.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B16.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B16.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B16.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B16.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B16.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B16.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B16.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B16.count
