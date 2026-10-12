import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0044
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B07
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 60).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9194 16
def localParent : Nat → Option Row
 | 9194 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 18),[(31932,1)]⟩
 | 9195 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 19),[(31933,1)]⟩
 | 9196 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 20),[(31935,1)]⟩
 | 9197 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 21),[(31934,4),(31935,1)]⟩
 | 9198 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 22),[(31936,1)]⟩
 | 9199 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 23),[(31937,1)]⟩
 | 9200 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 24),[(31939,1)]⟩
 | 9201 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 25),[(31938,4),(31939,1)]⟩
 | 9202 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 26),[(31940,1)]⟩
 | 9203 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 27),[(31941,1)]⟩
 | 9204 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 28),[(31943,1)]⟩
 | 9205 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 29),[(31942,4),(31943,1)]⟩
 | 9206 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 30),[(31944,1)]⟩
 | 9207 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 31),[(31945,1)]⟩
 | 9208 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 32),[(31947,1)]⟩
 | 9209 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 33),[(31946,4),(31947,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B07

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B07.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B07.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B07.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B07.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B07.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B07.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B07.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B07.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B07.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B07.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B07.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B07.count
