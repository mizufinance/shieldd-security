import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0021
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B09
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 92).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4562 16
def localParent : Nat → Option Row
 | 4562 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 60),[(27300,1)]⟩
 | 4563 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 61),[(27301,1)]⟩
 | 4564 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 62),[(27303,1)]⟩
 | 4565 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 63),[(27302,4),(27303,1)]⟩
 | 4566 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 64),[(27304,1)]⟩
 | 4567 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 65),[(27305,1)]⟩
 | 4568 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 66),[(27307,1)]⟩
 | 4569 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 67),[(27306,4),(27307,1)]⟩
 | 4570 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 68),[(27308,1)]⟩
 | 4571 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 69),[(27309,1)]⟩
 | 4572 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 70),[(27311,1)]⟩
 | 4573 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 71),[(27310,4),(27311,1)]⟩
 | 4574 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 72),[(27312,1)]⟩
 | 4575 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 73),[(27313,1)]⟩
 | 4576 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 74),[(27315,1)]⟩
 | 4577 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 75),[(27314,4),(27315,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B09

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B09.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B09.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B09.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B09.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B09.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B09.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B09.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B09.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B09.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B09.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B09.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B09.count
