import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0027
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B23
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 316).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5634 16
def localParent : Nat → Option Row
 | 5634 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 20),[(28372,1)]⟩
 | 5635 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 21),[(28373,1)]⟩
 | 5636 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 22),[(28375,1)]⟩
 | 5637 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 23),[(28374,4),(28375,1)]⟩
 | 5638 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 24),[(28376,1)]⟩
 | 5639 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 25),[(28377,1)]⟩
 | 5640 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 26),[(28379,1)]⟩
 | 5641 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 27),[(28378,4),(28379,1)]⟩
 | 5642 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 28),[(28380,1)]⟩
 | 5643 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 29),[(28381,1)]⟩
 | 5644 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 30),[(28383,1)]⟩
 | 5645 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 31),[(28382,4),(28383,1)]⟩
 | 5646 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 32),[(28384,1)]⟩
 | 5647 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 33),[(28385,1)]⟩
 | 5648 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 34),[(28387,1)]⟩
 | 5649 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 35),[(28386,4),(28387,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B23

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B23.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B23.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B23.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B23.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B23.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B23.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B23.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B23.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B23.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B23.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B23.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B23.count
