import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0042
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B14
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 172).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8882 16
def localParent : Nat → Option Row
 | 8882 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 92),[(31620,1)]⟩
 | 8883 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 93),[(31621,1)]⟩
 | 8884 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 94),[(31623,1)]⟩
 | 8885 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 95),[(31622,4),(31623,1)]⟩
 | 8886 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 96),[(31624,1)]⟩
 | 8887 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 97),[(31625,1)]⟩
 | 8888 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 98),[(31627,1)]⟩
 | 8889 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 99),[(31626,4),(31627,1)]⟩
 | 8890 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 100),[(31628,1)]⟩
 | 8891 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 101),[(31629,1)]⟩
 | 8892 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 102),[(31631,1)]⟩
 | 8893 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 103),[(31630,4),(31631,1)]⟩
 | 8894 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 104),[(31632,1)]⟩
 | 8895 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 105),[(31633,1)]⟩
 | 8896 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 106),[(31635,1)]⟩
 | 8897 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 107),[(31634,4),(31635,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B14

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B14.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B14.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B14.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B14.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B14.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B14.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B14.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B14.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B14.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B14.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B14.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B14.count
