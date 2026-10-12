import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0035
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L09B20
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 268).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4664)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7282 16
def localParent : Nat → Option Row
 | 7282 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 2),[(30020,1)]⟩
 | 7283 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 3),[(30021,1)]⟩
 | 7284 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 4),[(30023,1)]⟩
 | 7285 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 5),[(30022,4),(30023,1)]⟩
 | 7286 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 6),[(30024,1)]⟩
 | 7287 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 7),[(30025,1)]⟩
 | 7288 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 8),[(30027,1)]⟩
 | 7289 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 9),[(30026,4),(30027,1)]⟩
 | 7290 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 10),[(30028,1)]⟩
 | 7291 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 11),[(30029,1)]⟩
 | 7292 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 12),[(30031,1)]⟩
 | 7293 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 13),[(30030,4),(30031,1)]⟩
 | 7294 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 14),[(30032,1)]⟩
 | 7295 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 15),[(30033,1)]⟩
 | 7296 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 16),[(30035,1)]⟩
 | 7297 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 17),[(30034,4),(30035,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L09B20

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B20.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B20.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B20.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B20.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B20.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B20.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B20.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B20.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B20.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B20.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B20.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B20.count
