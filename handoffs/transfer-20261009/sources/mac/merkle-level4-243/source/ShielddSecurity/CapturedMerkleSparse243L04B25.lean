import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0025
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B25
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 348).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5242 16
def localParent : Nat → Option Row
 | 5242 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 22),[(27980,1)]⟩
 | 5243 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 23),[(27981,1)]⟩
 | 5244 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 24),[(27983,1)]⟩
 | 5245 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 25),[(27982,4),(27983,1)]⟩
 | 5246 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 26),[(27984,1)]⟩
 | 5247 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 27),[(27985,1)]⟩
 | 5248 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 28),[(27987,1)]⟩
 | 5249 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 29),[(27986,4),(27987,1)]⟩
 | 5250 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 30),[(27988,1)]⟩
 | 5251 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 31),[(27989,1)]⟩
 | 5252 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 32),[(27991,1)]⟩
 | 5253 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 33),[(27990,4),(27991,1)]⟩
 | 5254 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 34),[(27992,1)]⟩
 | 5255 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 35),[(27993,1)]⟩
 | 5256 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 36),[(27995,1)]⟩
 | 5257 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 37),[(27994,4),(27995,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B25

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B25.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B25.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B25.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B25.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B25.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B25.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B25.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B25.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B25.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B25.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B25.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B25.count
