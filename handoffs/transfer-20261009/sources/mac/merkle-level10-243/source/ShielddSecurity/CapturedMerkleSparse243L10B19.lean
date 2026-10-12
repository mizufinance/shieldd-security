import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0036
import ShielddSecurity.CapturedArithmetic45B0037
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B19
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 252).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7690 16
def localParent : Nat → Option Row
 | 7690 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 110),[(30428,1)]⟩
 | 7691 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 111),[(30429,1)]⟩
 | 7692 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 112),[(30431,1)]⟩
 | 7693 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 113),[(30430,4),(30431,1)]⟩
 | 7694 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 114),[(30432,1)]⟩
 | 7695 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 115),[(30433,1)]⟩
 | 7696 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 0),[(30435,1)]⟩
 | 7697 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 1),[(30434,4),(30435,1)]⟩
 | 7698 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 2),[(30436,1)]⟩
 | 7699 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 3),[(30437,1)]⟩
 | 7700 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 4),[(30439,1)]⟩
 | 7701 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 5),[(30438,4),(30439,1)]⟩
 | 7702 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 6),[(30440,1)]⟩
 | 7703 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 7),[(30441,1)]⟩
 | 7704 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 8),[(30443,1)]⟩
 | 7705 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 9),[(30442,4),(30443,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B19

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B19.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B19.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B19.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B19.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B19.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B19.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B19.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B19.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B19.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B19.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B19.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B19.count
