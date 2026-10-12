import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0037
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L11B04
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 12).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5512)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7874 16
def localParent : Nat → Option Row
 | 7874 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 178),[(30612,1)]⟩
 | 7875 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 179),[(30613,1)]⟩
 | 7876 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 180),[(30615,1)]⟩
 | 7877 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 181),[(30614,4),(30615,1)]⟩
 | 7878 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 182),[(30616,1)]⟩
 | 7879 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 183),[(30617,1)]⟩
 | 7880 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 184),[(30619,1)]⟩
 | 7881 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 185),[(30618,4),(30619,1)]⟩
 | 7882 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 186),[(30620,1)]⟩
 | 7883 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 187),[(30621,1)]⟩
 | 7884 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 188),[(30623,1)]⟩
 | 7885 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 189),[(30622,4),(30623,1)]⟩
 | 7886 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 190),[(30624,1)]⟩
 | 7887 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 191),[(30625,1)]⟩
 | 7888 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 192),[(30627,1)]⟩
 | 7889 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 193),[(30626,4),(30627,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L11B04

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B04.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B04.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B04.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B04.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B04.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B04.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B04.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B04.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B04.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B04.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B04.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B04.count
