import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0035
import ShielddSecurity.CapturedArithmetic45B0036
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B12
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 140).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7578 16
def localParent : Nat → Option Row
 | 7578 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 298),[(30316,1)]⟩
 | 7579 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 299),[(30317,1)]⟩
 | 7580 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 0),[(30319,1)]⟩
 | 7581 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 1),[(30318,4),(30319,1)]⟩
 | 7582 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 2),[(30320,1)]⟩
 | 7583 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 3),[(30321,1)]⟩
 | 7584 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 4),[(30323,1)]⟩
 | 7585 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 5),[(30322,4),(30323,1)]⟩
 | 7586 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 6),[(30324,1)]⟩
 | 7587 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 7),[(30325,1)]⟩
 | 7588 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 8),[(30327,1)]⟩
 | 7589 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 9),[(30326,4),(30327,1)]⟩
 | 7590 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 10),[(30328,1)]⟩
 | 7591 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 11),[(30329,1)]⟩
 | 7592 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 12),[(30331,1)]⟩
 | 7593 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 13),[(30330,4),(30331,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B12

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B12.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B12.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B12.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B12.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B12.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B12.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B12.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B12.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B12.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B12.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B12.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B12.count
