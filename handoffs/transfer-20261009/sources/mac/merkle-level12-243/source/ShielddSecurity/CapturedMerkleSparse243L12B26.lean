import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0041
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B26
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 364).take 8).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8650 8
def localParent : Nat → Option Row
 | 8650 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 122),[(31388,1)]⟩
 | 8651 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 123),[(31389,1)]⟩
 | 8652 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 124),[(31391,1)]⟩
 | 8653 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 125),[(31390,4),(31391,1)]⟩
 | 8654 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 126),[(31392,1)]⟩
 | 8655 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 127),[(31393,1)]⟩
 | 8656 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 128),[(31395,1)]⟩
 | 8657 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 129),[(31394,4),(31395,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=8 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B26

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B26.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B26.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B26.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B26.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B26.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B26.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B26.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B26.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B26.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B26.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B26.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B26.count
