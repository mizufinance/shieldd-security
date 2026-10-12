import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0037
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B26
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 364).take 8).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7802 8
def localParent : Nat → Option Row
 | 7802 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 106),[(30540,1)]⟩
 | 7803 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 107),[(30541,1)]⟩
 | 7804 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 108),[(30543,1)]⟩
 | 7805 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 109),[(30542,4),(30543,1)]⟩
 | 7806 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 110),[(30544,1)]⟩
 | 7807 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 111),[(30545,1)]⟩
 | 7808 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 112),[(30547,1)]⟩
 | 7809 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 113),[(30546,4),(30547,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=8 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B26

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B26.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B26.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B26.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B26.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B26.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B26.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B26.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B26.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B26.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B26.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B26.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B26.count
