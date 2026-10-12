import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0043
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B23
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 316).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9026 16
def localParent : Nat → Option Row
 | 9026 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 82),[(31764,1)]⟩
 | 9027 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 83),[(31765,1)]⟩
 | 9028 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 84),[(31767,1)]⟩
 | 9029 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 85),[(31766,4),(31767,1)]⟩
 | 9030 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 86),[(31768,1)]⟩
 | 9031 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 87),[(31769,1)]⟩
 | 9032 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 88),[(31771,1)]⟩
 | 9033 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 89),[(31770,4),(31771,1)]⟩
 | 9034 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 90),[(31772,1)]⟩
 | 9035 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 91),[(31773,1)]⟩
 | 9036 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 92),[(31775,1)]⟩
 | 9037 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 93),[(31774,4),(31775,1)]⟩
 | 9038 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 94),[(31776,1)]⟩
 | 9039 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 95),[(31777,1)]⟩
 | 9040 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 96),[(31779,1)]⟩
 | 9041 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 97),[(31778,4),(31779,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B23

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B23.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B23.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B23.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B23.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B23.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B23.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B23.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B23.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B23.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B23.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B23.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B23.count
