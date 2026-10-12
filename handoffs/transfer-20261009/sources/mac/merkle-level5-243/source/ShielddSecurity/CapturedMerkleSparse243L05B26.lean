import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0027
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B26
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 364).take 8).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5682 8
def localParent : Nat → Option Row
 | 5682 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 68),[(28420,1)]⟩
 | 5683 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 69),[(28421,1)]⟩
 | 5684 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 70),[(28423,1)]⟩
 | 5685 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 71),[(28422,4),(28423,1)]⟩
 | 5686 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 72),[(28424,1)]⟩
 | 5687 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 73),[(28425,1)]⟩
 | 5688 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 74),[(28427,1)]⟩
 | 5689 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 75),[(28426,4),(28427,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=8 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B26

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B26.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B26.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B26.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B26.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B26.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B26.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B26.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B26.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B26.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B26.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B26.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B26.count
