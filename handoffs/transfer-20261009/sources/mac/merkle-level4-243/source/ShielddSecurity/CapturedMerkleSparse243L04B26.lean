import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0025
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B26
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 364).take 8).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5258 8
def localParent : Nat → Option Row
 | 5258 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 38),[(27996,1)]⟩
 | 5259 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 39),[(27997,1)]⟩
 | 5260 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 40),[(27999,1)]⟩
 | 5261 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 41),[(27998,4),(27999,1)]⟩
 | 5262 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 42),[(28000,1)]⟩
 | 5263 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 43),[(28001,1)]⟩
 | 5264 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 44),[(28003,1)]⟩
 | 5265 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 45),[(28002,4),(28003,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=8 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B26

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B26.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B26.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B26.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B26.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B26.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B26.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B26.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B26.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B26.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B26.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B26.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B26.count
