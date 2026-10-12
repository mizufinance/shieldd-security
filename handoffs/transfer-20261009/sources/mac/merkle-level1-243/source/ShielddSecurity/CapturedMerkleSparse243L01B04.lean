import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0016
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L01B04
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 12).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1272)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3634 16
def localParent : Nat → Option Row
 | 3634 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 188),[(26372,1)]⟩
 | 3635 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 189),[(26373,1)]⟩
 | 3636 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 190),[(26375,1)]⟩
 | 3637 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 191),[(26374,4),(26375,1)]⟩
 | 3638 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 192),[(26376,1)]⟩
 | 3639 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 193),[(26377,1)]⟩
 | 3640 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 194),[(26379,1)]⟩
 | 3641 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 195),[(26378,4),(26379,1)]⟩
 | 3642 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 196),[(26380,1)]⟩
 | 3643 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 197),[(26381,1)]⟩
 | 3644 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 198),[(26383,1)]⟩
 | 3645 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 199),[(26382,4),(26383,1)]⟩
 | 3646 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 200),[(26384,1)]⟩
 | 3647 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 201),[(26385,1)]⟩
 | 3648 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 202),[(26387,1)]⟩
 | 3649 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 203),[(26386,4),(26387,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L01B04

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B04.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B04.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B04.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B04.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B04.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B04.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B04.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B04.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B04.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B04.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B04.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B04.count
