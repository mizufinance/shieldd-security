import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0023
import ShielddSecurity.CapturedArithmetic45B0024
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B16
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 204).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5098 16
def localParent : Nat → Option Row
 | 5098 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 234),[(27836,1)]⟩
 | 5099 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 235),[(27837,1)]⟩
 | 5100 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 236),[(27839,1)]⟩
 | 5101 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 237),[(27838,4),(27839,1)]⟩
 | 5102 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 238),[(27840,1)]⟩
 | 5103 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 239),[(27841,1)]⟩
 | 5104 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 240),[(27843,1)]⟩
 | 5105 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 241),[(27842,4),(27843,1)]⟩
 | 5106 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 242),[(27844,1)]⟩
 | 5107 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 243),[(27845,1)]⟩
 | 5108 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 0),[(27847,1)]⟩
 | 5109 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 1),[(27846,4),(27847,1)]⟩
 | 5110 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 2),[(27848,1)]⟩
 | 5111 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 3),[(27849,1)]⟩
 | 5112 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 4),[(27851,1)]⟩
 | 5113 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 5),[(27850,4),(27851,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B16

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B16.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B16.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B16.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B16.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B16.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B16.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B16.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B16.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B16.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B16.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B16.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B16.count
