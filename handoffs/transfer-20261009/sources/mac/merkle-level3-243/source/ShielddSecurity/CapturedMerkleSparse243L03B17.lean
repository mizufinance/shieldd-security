import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0021
import ShielddSecurity.CapturedArithmetic45B0022
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B17
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 220).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4690 16
def localParent : Nat → Option Row
 | 4690 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 188),[(27428,1)]⟩
 | 4691 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 189),[(27429,1)]⟩
 | 4692 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 190),[(27431,1)]⟩
 | 4693 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 191),[(27430,4),(27431,1)]⟩
 | 4694 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 0),[(27432,1)]⟩
 | 4695 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 1),[(27433,1)]⟩
 | 4696 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 2),[(27435,1)]⟩
 | 4697 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 3),[(27434,4),(27435,1)]⟩
 | 4698 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 4),[(27436,1)]⟩
 | 4699 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 5),[(27437,1)]⟩
 | 4700 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 6),[(27439,1)]⟩
 | 4701 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 7),[(27438,4),(27439,1)]⟩
 | 4702 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 8),[(27440,1)]⟩
 | 4703 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 9),[(27441,1)]⟩
 | 4704 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 10),[(27443,1)]⟩
 | 4705 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 11),[(27442,4),(27443,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B17

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B17.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B17.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B17.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B17.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B17.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B17.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B17.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B17.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B17.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B17.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B17.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B17.count
