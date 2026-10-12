import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0038
import ShielddSecurity.CapturedArithmetic45B0039
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L11B18
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 236).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5512)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8098 16
def localParent : Nat → Option Row
 | 8098 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 112),[(30836,1)]⟩
 | 8099 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 113),[(30837,1)]⟩
 | 8100 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 114),[(30839,1)]⟩
 | 8101 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 115),[(30838,4),(30839,1)]⟩
 | 8102 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 116),[(30840,1)]⟩
 | 8103 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 117),[(30841,1)]⟩
 | 8104 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 118),[(30843,1)]⟩
 | 8105 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 119),[(30842,4),(30843,1)]⟩
 | 8106 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 120),[(30844,1)]⟩
 | 8107 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 121),[(30845,1)]⟩
 | 8108 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 122),[(30847,1)]⟩
 | 8109 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 123),[(30846,4),(30847,1)]⟩
 | 8110 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 124),[(30848,1)]⟩
 | 8111 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 125),[(30849,1)]⟩
 | 8112 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 0),[(30851,1)]⟩
 | 8113 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 1),[(30850,4),(30851,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L11B18

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B18.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B18.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B18.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B18.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B18.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B18.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B18.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B18.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B18.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B18.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B18.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B18.count
