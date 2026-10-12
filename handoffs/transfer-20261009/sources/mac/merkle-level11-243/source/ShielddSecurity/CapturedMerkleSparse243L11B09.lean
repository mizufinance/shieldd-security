import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0037
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L11B09
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 92).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5512)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7954 16
def localParent : Nat → Option Row
 | 7954 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 258),[(30692,1)]⟩
 | 7955 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 259),[(30693,1)]⟩
 | 7956 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 260),[(30695,1)]⟩
 | 7957 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 261),[(30694,4),(30695,1)]⟩
 | 7958 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 262),[(30696,1)]⟩
 | 7959 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 263),[(30697,1)]⟩
 | 7960 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 264),[(30699,1)]⟩
 | 7961 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 265),[(30698,4),(30699,1)]⟩
 | 7962 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 266),[(30700,1)]⟩
 | 7963 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 267),[(30701,1)]⟩
 | 7964 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 268),[(30703,1)]⟩
 | 7965 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 269),[(30702,4),(30703,1)]⟩
 | 7966 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 270),[(30704,1)]⟩
 | 7967 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 271),[(30705,1)]⟩
 | 7968 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 272),[(30707,1)]⟩
 | 7969 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 273),[(30706,4),(30707,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L11B09

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B09.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B09.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B09.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B09.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B09.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B09.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B09.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B09.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B09.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B09.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B09.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B09.count
