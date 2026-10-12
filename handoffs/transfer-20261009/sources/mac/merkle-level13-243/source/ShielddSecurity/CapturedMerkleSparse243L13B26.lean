import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0043
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B26
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 364).take 8).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9074 8
def localParent : Nat → Option Row
 | 9074 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 130),[(31812,1)]⟩
 | 9075 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 131),[(31813,1)]⟩
 | 9076 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 132),[(31815,1)]⟩
 | 9077 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 133),[(31814,4),(31815,1)]⟩
 | 9078 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 134),[(31816,1)]⟩
 | 9079 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 135),[(31817,1)]⟩
 | 9080 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 136),[(31819,1)]⟩
 | 9081 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 137),[(31818,4),(31819,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=8 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B26

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B26.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B26.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B26.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B26.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B26.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B26.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B26.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B26.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B26.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B26.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B26.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B26.count
