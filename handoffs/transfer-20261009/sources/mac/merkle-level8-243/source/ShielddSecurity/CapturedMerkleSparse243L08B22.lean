import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0033
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B22
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 300).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6890 16
def localParent : Nat → Option Row
 | 6890 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 26),[(29628,1)]⟩
 | 6891 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 27),[(29629,1)]⟩
 | 6892 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 28),[(29631,1)]⟩
 | 6893 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 29),[(29630,4),(29631,1)]⟩
 | 6894 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 30),[(29632,1)]⟩
 | 6895 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 31),[(29633,1)]⟩
 | 6896 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 32),[(29635,1)]⟩
 | 6897 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 33),[(29634,4),(29635,1)]⟩
 | 6898 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 34),[(29636,1)]⟩
 | 6899 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 35),[(29637,1)]⟩
 | 6900 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 36),[(29639,1)]⟩
 | 6901 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 37),[(29638,4),(29639,1)]⟩
 | 6902 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 38),[(29640,1)]⟩
 | 6903 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 39),[(29641,1)]⟩
 | 6904 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 40),[(29643,1)]⟩
 | 6905 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 41),[(29642,4),(29643,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B22

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B22.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B22.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B22.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B22.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B22.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B22.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B22.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B22.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B22.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B22.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B22.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B22.count
