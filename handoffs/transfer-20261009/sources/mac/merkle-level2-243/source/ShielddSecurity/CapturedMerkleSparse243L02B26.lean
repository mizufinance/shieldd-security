import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0020
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B26
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 364).take 8).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4410 8
def localParent : Nat → Option Row
 | 4410 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 132),[(27148,1)]⟩
 | 4411 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 133),[(27149,1)]⟩
 | 4412 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 134),[(27151,1)]⟩
 | 4413 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 135),[(27150,4),(27151,1)]⟩
 | 4414 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 136),[(27152,1)]⟩
 | 4415 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 137),[(27153,1)]⟩
 | 4416 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 138),[(27155,1)]⟩
 | 4417 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 139),[(27154,4),(27155,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=8 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B26

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B26.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B26.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B26.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B26.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B26.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B26.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B26.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B26.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B26.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B26.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B26.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B26.count
