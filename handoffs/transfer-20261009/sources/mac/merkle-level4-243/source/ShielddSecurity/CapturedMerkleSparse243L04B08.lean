import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0023
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B08
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 76).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4970 16
def localParent : Nat → Option Row
 | 4970 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 106),[(27708,1)]⟩
 | 4971 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 107),[(27709,1)]⟩
 | 4972 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 108),[(27711,1)]⟩
 | 4973 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 109),[(27710,4),(27711,1)]⟩
 | 4974 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 110),[(27712,1)]⟩
 | 4975 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 111),[(27713,1)]⟩
 | 4976 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 112),[(27715,1)]⟩
 | 4977 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 113),[(27714,4),(27715,1)]⟩
 | 4978 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 114),[(27716,1)]⟩
 | 4979 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 115),[(27717,1)]⟩
 | 4980 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 116),[(27719,1)]⟩
 | 4981 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 117),[(27718,4),(27719,1)]⟩
 | 4982 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 118),[(27720,1)]⟩
 | 4983 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 119),[(27721,1)]⟩
 | 4984 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 120),[(27723,1)]⟩
 | 4985 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 121),[(27722,4),(27723,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B08

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B08.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B08.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B08.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B08.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B08.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B08.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B08.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B08.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B08.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B08.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B08.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B08.count
