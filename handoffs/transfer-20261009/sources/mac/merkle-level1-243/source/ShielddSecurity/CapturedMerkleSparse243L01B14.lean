import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0017
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L01B14
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 172).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1272)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3794 16
def localParent : Nat → Option Row
 | 3794 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 70),[(26532,1)]⟩
 | 3795 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 71),[(26533,1)]⟩
 | 3796 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 72),[(26535,1)]⟩
 | 3797 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 73),[(26534,4),(26535,1)]⟩
 | 3798 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 74),[(26536,1)]⟩
 | 3799 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 75),[(26537,1)]⟩
 | 3800 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 76),[(26539,1)]⟩
 | 3801 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 77),[(26538,4),(26539,1)]⟩
 | 3802 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 78),[(26540,1)]⟩
 | 3803 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 79),[(26541,1)]⟩
 | 3804 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 80),[(26543,1)]⟩
 | 3805 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 81),[(26542,4),(26543,1)]⟩
 | 3806 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 82),[(26544,1)]⟩
 | 3807 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 83),[(26545,1)]⟩
 | 3808 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 84),[(26547,1)]⟩
 | 3809 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 85),[(26546,4),(26547,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L01B14

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B14.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B14.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B14.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B14.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B14.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B14.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B14.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B14.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B14.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B14.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B14.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B14.count
