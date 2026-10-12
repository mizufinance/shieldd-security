import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0033
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B21
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 284).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6874 16
def localParent : Nat → Option Row
 | 6874 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 10),[(29612,1)]⟩
 | 6875 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 11),[(29613,1)]⟩
 | 6876 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 12),[(29615,1)]⟩
 | 6877 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 13),[(29614,4),(29615,1)]⟩
 | 6878 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 14),[(29616,1)]⟩
 | 6879 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 15),[(29617,1)]⟩
 | 6880 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 16),[(29619,1)]⟩
 | 6881 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 17),[(29618,4),(29619,1)]⟩
 | 6882 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 18),[(29620,1)]⟩
 | 6883 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 19),[(29621,1)]⟩
 | 6884 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 20),[(29623,1)]⟩
 | 6885 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 21),[(29622,4),(29623,1)]⟩
 | 6886 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 22),[(29624,1)]⟩
 | 6887 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 23),[(29625,1)]⟩
 | 6888 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 24),[(29627,1)]⟩
 | 6889 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 25),[(29626,4),(29627,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B21

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B21.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B21.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B21.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B21.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B21.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B21.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B21.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B21.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B21.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B21.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B21.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B21.count
