import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0043
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B04
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 12).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9146 16
def localParent : Nat → Option Row
 | 9146 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 202),[(31884,1)]⟩
 | 9147 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 203),[(31885,1)]⟩
 | 9148 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 204),[(31887,1)]⟩
 | 9149 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 205),[(31886,4),(31887,1)]⟩
 | 9150 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 206),[(31888,1)]⟩
 | 9151 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 207),[(31889,1)]⟩
 | 9152 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 208),[(31891,1)]⟩
 | 9153 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 209),[(31890,4),(31891,1)]⟩
 | 9154 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 210),[(31892,1)]⟩
 | 9155 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 211),[(31893,1)]⟩
 | 9156 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 212),[(31895,1)]⟩
 | 9157 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 213),[(31894,4),(31895,1)]⟩
 | 9158 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 214),[(31896,1)]⟩
 | 9159 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 215),[(31897,1)]⟩
 | 9160 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 216),[(31899,1)]⟩
 | 9161 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 217),[(31898,4),(31899,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B04

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B04.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B04.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B04.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B04.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B04.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B04.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B04.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B04.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B04.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B04.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B04.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B04.count
