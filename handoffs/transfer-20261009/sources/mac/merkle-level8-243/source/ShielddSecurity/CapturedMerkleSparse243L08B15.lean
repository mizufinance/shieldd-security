import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0032
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B15
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 188).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6778 16
def localParent : Nat → Option Row
 | 6778 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 18),[(29516,1)]⟩
 | 6779 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 19),[(29517,1)]⟩
 | 6780 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 20),[(29519,1)]⟩
 | 6781 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 21),[(29518,4),(29519,1)]⟩
 | 6782 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 22),[(29520,1)]⟩
 | 6783 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 23),[(29521,1)]⟩
 | 6784 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 24),[(29523,1)]⟩
 | 6785 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 25),[(29522,4),(29523,1)]⟩
 | 6786 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 26),[(29524,1)]⟩
 | 6787 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 27),[(29525,1)]⟩
 | 6788 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 28),[(29527,1)]⟩
 | 6789 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 29),[(29526,4),(29527,1)]⟩
 | 6790 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 30),[(29528,1)]⟩
 | 6791 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 31),[(29529,1)]⟩
 | 6792 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 32),[(29531,1)]⟩
 | 6793 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 33),[(29530,4),(29531,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B15

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B15.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B15.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B15.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B15.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B15.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B15.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B15.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B15.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B15.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B15.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B15.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B15.count
