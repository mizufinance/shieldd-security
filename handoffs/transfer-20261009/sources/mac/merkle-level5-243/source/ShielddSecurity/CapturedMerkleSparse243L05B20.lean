import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0026
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B20
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 268).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5586 16
def localParent : Nat → Option Row
 | 5586 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 64),[(28324,1)]⟩
 | 5587 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 65),[(28325,1)]⟩
 | 5588 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 66),[(28327,1)]⟩
 | 5589 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 67),[(28326,4),(28327,1)]⟩
 | 5590 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 68),[(28328,1)]⟩
 | 5591 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 69),[(28329,1)]⟩
 | 5592 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 70),[(28331,1)]⟩
 | 5593 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 71),[(28330,4),(28331,1)]⟩
 | 5594 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 72),[(28332,1)]⟩
 | 5595 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 73),[(28333,1)]⟩
 | 5596 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 74),[(28335,1)]⟩
 | 5597 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 75),[(28334,4),(28335,1)]⟩
 | 5598 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 76),[(28336,1)]⟩
 | 5599 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 77),[(28337,1)]⟩
 | 5600 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 78),[(28339,1)]⟩
 | 5601 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 79),[(28338,4),(28339,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B20

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B20.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B20.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B20.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B20.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B20.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B20.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B20.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B20.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B20.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B20.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B20.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B20.count
