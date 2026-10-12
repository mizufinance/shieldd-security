import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0029
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B26
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 364).take 8).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6106 8
def localParent : Nat → Option Row
 | 6106 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 76),[(28844,1)]⟩
 | 6107 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 77),[(28845,1)]⟩
 | 6108 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 78),[(28847,1)]⟩
 | 6109 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 79),[(28846,4),(28847,1)]⟩
 | 6110 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 80),[(28848,1)]⟩
 | 6111 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 81),[(28849,1)]⟩
 | 6112 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 82),[(28851,1)]⟩
 | 6113 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 83),[(28850,4),(28851,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=8 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B26

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B26.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B26.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B26.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B26.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B26.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B26.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B26.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B26.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B26.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B26.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B26.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B26.count
