import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0015
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L00B17
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 220).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 848)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3418 16
def localParent : Nat → Option Row
 | 3418 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 98),[(26156,1)]⟩
 | 3419 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 99),[(26157,1)]⟩
 | 3420 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 100),[(26159,1)]⟩
 | 3421 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 101),[(26158,4),(26159,1)]⟩
 | 3422 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 102),[(26160,1)]⟩
 | 3423 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 103),[(26161,1)]⟩
 | 3424 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 104),[(26163,1)]⟩
 | 3425 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 105),[(26162,4),(26163,1)]⟩
 | 3426 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 106),[(26164,1)]⟩
 | 3427 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 107),[(26165,1)]⟩
 | 3428 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 108),[(26167,1)]⟩
 | 3429 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 109),[(26166,4),(26167,1)]⟩
 | 3430 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 110),[(26168,1)]⟩
 | 3431 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 111),[(26169,1)]⟩
 | 3432 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 112),[(26171,1)]⟩
 | 3433 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 113),[(26170,4),(26171,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L00B17

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B17.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B17.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B17.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B17.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B17.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B17.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B17.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B17.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B17.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B17.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B17.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B17.count
