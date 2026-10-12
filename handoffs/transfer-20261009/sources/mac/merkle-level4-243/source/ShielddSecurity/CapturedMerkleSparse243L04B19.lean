import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0024
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B19
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 252).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5146 16
def localParent : Nat → Option Row
 | 5146 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 38),[(27884,1)]⟩
 | 5147 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 39),[(27885,1)]⟩
 | 5148 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 40),[(27887,1)]⟩
 | 5149 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 41),[(27886,4),(27887,1)]⟩
 | 5150 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 42),[(27888,1)]⟩
 | 5151 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 43),[(27889,1)]⟩
 | 5152 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 44),[(27891,1)]⟩
 | 5153 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 45),[(27890,4),(27891,1)]⟩
 | 5154 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 46),[(27892,1)]⟩
 | 5155 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 47),[(27893,1)]⟩
 | 5156 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 48),[(27895,1)]⟩
 | 5157 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 49),[(27894,4),(27895,1)]⟩
 | 5158 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 50),[(27896,1)]⟩
 | 5159 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 51),[(27897,1)]⟩
 | 5160 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 52),[(27899,1)]⟩
 | 5161 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 53),[(27898,4),(27899,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B19

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B19.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B19.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B19.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B19.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B19.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B19.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B19.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B19.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B19.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B19.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B19.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B19.count
