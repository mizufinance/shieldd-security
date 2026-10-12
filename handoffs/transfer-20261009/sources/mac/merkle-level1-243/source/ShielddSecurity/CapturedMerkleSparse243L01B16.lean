import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0017
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L01B16
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 204).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1272)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3826 16
def localParent : Nat → Option Row
 | 3826 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 102),[(26564,1)]⟩
 | 3827 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 103),[(26565,1)]⟩
 | 3828 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 104),[(26567,1)]⟩
 | 3829 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 105),[(26566,4),(26567,1)]⟩
 | 3830 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 106),[(26568,1)]⟩
 | 3831 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 107),[(26569,1)]⟩
 | 3832 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 108),[(26571,1)]⟩
 | 3833 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 109),[(26570,4),(26571,1)]⟩
 | 3834 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 110),[(26572,1)]⟩
 | 3835 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 111),[(26573,1)]⟩
 | 3836 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 112),[(26575,1)]⟩
 | 3837 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 113),[(26574,4),(26575,1)]⟩
 | 3838 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 114),[(26576,1)]⟩
 | 3839 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 115),[(26577,1)]⟩
 | 3840 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 116),[(26579,1)]⟩
 | 3841 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 117),[(26578,4),(26579,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L01B16

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B16.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B16.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B16.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B16.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B16.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B16.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B16.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B16.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B16.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B16.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B16.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B16.count
