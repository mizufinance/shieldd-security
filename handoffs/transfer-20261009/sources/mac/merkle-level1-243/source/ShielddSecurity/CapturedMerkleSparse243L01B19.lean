import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0018
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L01B19
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 252).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1272)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3874 16
def localParent : Nat → Option Row
 | 3874 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 12),[(26612,1)]⟩
 | 3875 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 13),[(26613,1)]⟩
 | 3876 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 14),[(26615,1)]⟩
 | 3877 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 15),[(26614,4),(26615,1)]⟩
 | 3878 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 16),[(26616,1)]⟩
 | 3879 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 17),[(26617,1)]⟩
 | 3880 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 18),[(26619,1)]⟩
 | 3881 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 19),[(26618,4),(26619,1)]⟩
 | 3882 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 20),[(26620,1)]⟩
 | 3883 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 21),[(26621,1)]⟩
 | 3884 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 22),[(26623,1)]⟩
 | 3885 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 23),[(26622,4),(26623,1)]⟩
 | 3886 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 24),[(26624,1)]⟩
 | 3887 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 25),[(26625,1)]⟩
 | 3888 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 26),[(26627,1)]⟩
 | 3889 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 27),[(26626,4),(26627,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L01B19

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B19.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B19.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B19.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B19.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B19.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B19.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B19.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B19.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B19.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B19.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B19.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B19.count
