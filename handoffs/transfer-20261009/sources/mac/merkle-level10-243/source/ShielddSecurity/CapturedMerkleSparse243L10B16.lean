import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0036
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B16
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 204).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7642 16
def localParent : Nat → Option Row
 | 7642 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 62),[(30380,1)]⟩
 | 7643 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 63),[(30381,1)]⟩
 | 7644 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 64),[(30383,1)]⟩
 | 7645 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 65),[(30382,4),(30383,1)]⟩
 | 7646 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 66),[(30384,1)]⟩
 | 7647 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 67),[(30385,1)]⟩
 | 7648 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 68),[(30387,1)]⟩
 | 7649 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 69),[(30386,4),(30387,1)]⟩
 | 7650 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 70),[(30388,1)]⟩
 | 7651 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 71),[(30389,1)]⟩
 | 7652 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 72),[(30391,1)]⟩
 | 7653 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 73),[(30390,4),(30391,1)]⟩
 | 7654 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 74),[(30392,1)]⟩
 | 7655 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 75),[(30393,1)]⟩
 | 7656 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 76),[(30395,1)]⟩
 | 7657 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 77),[(30394,4),(30395,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B16

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B16.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B16.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B16.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B16.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B16.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B16.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B16.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B16.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B16.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B16.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B16.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B16.count
