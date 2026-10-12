import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0045
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B22
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 300).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9434 16
def localParent : Nat → Option Row
 | 9434 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 74),[(32172,1)]⟩
 | 9435 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 75),[(32173,1)]⟩
 | 9436 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 76),[(32175,1)]⟩
 | 9437 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 77),[(32174,4),(32175,1)]⟩
 | 9438 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 78),[(32176,1)]⟩
 | 9439 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 79),[(32177,1)]⟩
 | 9440 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 80),[(32179,1)]⟩
 | 9441 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 81),[(32178,4),(32179,1)]⟩
 | 9442 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 82),[(32180,1)]⟩
 | 9443 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 83),[(32181,1)]⟩
 | 9444 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 84),[(32183,1)]⟩
 | 9445 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 85),[(32182,4),(32183,1)]⟩
 | 9446 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 86),[(32184,1)]⟩
 | 9447 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 87),[(32185,1)]⟩
 | 9448 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 88),[(32187,1)]⟩
 | 9449 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 89),[(32186,4),(32187,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B22

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B22.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B22.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B22.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B22.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B22.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B22.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B22.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B22.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B22.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B22.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B22.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B22.count
