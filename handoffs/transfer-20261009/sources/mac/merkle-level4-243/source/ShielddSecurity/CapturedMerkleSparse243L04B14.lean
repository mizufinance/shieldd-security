import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0023
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B14
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 172).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5066 16
def localParent : Nat → Option Row
 | 5066 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 202),[(27804,1)]⟩
 | 5067 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 203),[(27805,1)]⟩
 | 5068 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 204),[(27807,1)]⟩
 | 5069 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 205),[(27806,4),(27807,1)]⟩
 | 5070 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 206),[(27808,1)]⟩
 | 5071 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 207),[(27809,1)]⟩
 | 5072 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 208),[(27811,1)]⟩
 | 5073 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 209),[(27810,4),(27811,1)]⟩
 | 5074 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 210),[(27812,1)]⟩
 | 5075 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 211),[(27813,1)]⟩
 | 5076 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 212),[(27815,1)]⟩
 | 5077 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 213),[(27814,4),(27815,1)]⟩
 | 5078 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 214),[(27816,1)]⟩
 | 5079 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 215),[(27817,1)]⟩
 | 5080 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 216),[(27819,1)]⟩
 | 5081 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 217),[(27818,4),(27819,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B14

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B14.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B14.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B14.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B14.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B14.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B14.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B14.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B14.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B14.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B14.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B14.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B14.count
