import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0043
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B24
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 332).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9042 16
def localParent : Nat → Option Row
 | 9042 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 98),[(31780,1)]⟩
 | 9043 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 99),[(31781,1)]⟩
 | 9044 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 100),[(31783,1)]⟩
 | 9045 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 101),[(31782,4),(31783,1)]⟩
 | 9046 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 102),[(31784,1)]⟩
 | 9047 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 103),[(31785,1)]⟩
 | 9048 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 104),[(31787,1)]⟩
 | 9049 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 105),[(31786,4),(31787,1)]⟩
 | 9050 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 106),[(31788,1)]⟩
 | 9051 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 107),[(31789,1)]⟩
 | 9052 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 108),[(31791,1)]⟩
 | 9053 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 109),[(31790,4),(31791,1)]⟩
 | 9054 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 110),[(31792,1)]⟩
 | 9055 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 111),[(31793,1)]⟩
 | 9056 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 112),[(31795,1)]⟩
 | 9057 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 113),[(31794,4),(31795,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B24

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B24.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B24.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B24.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B24.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B24.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B24.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B24.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B24.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B24.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B24.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B24.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B24.count
