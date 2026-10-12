import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0017
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L01B11
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 124).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1272)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3746 16
def localParent : Nat → Option Row
 | 3746 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 22),[(26484,1)]⟩
 | 3747 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 23),[(26485,1)]⟩
 | 3748 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 24),[(26487,1)]⟩
 | 3749 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 25),[(26486,4),(26487,1)]⟩
 | 3750 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 26),[(26488,1)]⟩
 | 3751 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 27),[(26489,1)]⟩
 | 3752 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 28),[(26491,1)]⟩
 | 3753 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 29),[(26490,4),(26491,1)]⟩
 | 3754 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 30),[(26492,1)]⟩
 | 3755 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 31),[(26493,1)]⟩
 | 3756 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 32),[(26495,1)]⟩
 | 3757 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 33),[(26494,4),(26495,1)]⟩
 | 3758 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 34),[(26496,1)]⟩
 | 3759 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 35),[(26497,1)]⟩
 | 3760 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 36),[(26499,1)]⟩
 | 3761 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 37),[(26498,4),(26499,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L01B11

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B11.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B11.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B11.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B11.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B11.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B11.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B11.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B11.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B11.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B11.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B11.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B11.count
