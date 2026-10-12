import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0039
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L11B26
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 364).take 8).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5512)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8226 8
def localParent : Nat → Option Row
 | 8226 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 114),[(30964,1)]⟩
 | 8227 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 115),[(30965,1)]⟩
 | 8228 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 116),[(30967,1)]⟩
 | 8229 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 117),[(30966,4),(30967,1)]⟩
 | 8230 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 118),[(30968,1)]⟩
 | 8231 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 119),[(30969,1)]⟩
 | 8232 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 120),[(30971,1)]⟩
 | 8233 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 121),[(30970,4),(30971,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=8 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L11B26

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B26.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B26.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B26.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B26.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B26.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B26.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B26.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B26.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B26.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B26.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B26.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B26.count
