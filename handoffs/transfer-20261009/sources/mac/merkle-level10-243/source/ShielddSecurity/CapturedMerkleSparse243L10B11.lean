import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0035
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B11
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 124).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7562 16
def localParent : Nat → Option Row
 | 7562 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 282),[(30300,1)]⟩
 | 7563 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 283),[(30301,1)]⟩
 | 7564 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 284),[(30303,1)]⟩
 | 7565 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 285),[(30302,4),(30303,1)]⟩
 | 7566 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 286),[(30304,1)]⟩
 | 7567 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 287),[(30305,1)]⟩
 | 7568 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 288),[(30307,1)]⟩
 | 7569 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 289),[(30306,4),(30307,1)]⟩
 | 7570 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 290),[(30308,1)]⟩
 | 7571 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 291),[(30309,1)]⟩
 | 7572 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 292),[(30311,1)]⟩
 | 7573 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 293),[(30310,4),(30311,1)]⟩
 | 7574 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 294),[(30312,1)]⟩
 | 7575 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 295),[(30313,1)]⟩
 | 7576 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 296),[(30315,1)]⟩
 | 7577 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 297),[(30314,4),(30315,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B11

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B11.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B11.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B11.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B11.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B11.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B11.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B11.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B11.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B11.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B11.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B11.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B11.count
