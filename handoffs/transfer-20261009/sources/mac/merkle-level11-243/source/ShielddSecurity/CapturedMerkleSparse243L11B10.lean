import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0037
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L11B10
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 108).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5512)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7970 16
def localParent : Nat → Option Row
 | 7970 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 274),[(30708,1)]⟩
 | 7971 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 275),[(30709,1)]⟩
 | 7972 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 276),[(30711,1)]⟩
 | 7973 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 277),[(30710,4),(30711,1)]⟩
 | 7974 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 278),[(30712,1)]⟩
 | 7975 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 279),[(30713,1)]⟩
 | 7976 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 280),[(30715,1)]⟩
 | 7977 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 281),[(30714,4),(30715,1)]⟩
 | 7978 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 282),[(30716,1)]⟩
 | 7979 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 283),[(30717,1)]⟩
 | 7980 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 284),[(30719,1)]⟩
 | 7981 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 285),[(30718,4),(30719,1)]⟩
 | 7982 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 286),[(30720,1)]⟩
 | 7983 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 287),[(30721,1)]⟩
 | 7984 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 288),[(30723,1)]⟩
 | 7985 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 289),[(30722,4),(30723,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L11B10

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B10.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B10.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B10.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B10.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B10.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B10.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B10.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B10.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B10.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B10.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B10.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B10.count
