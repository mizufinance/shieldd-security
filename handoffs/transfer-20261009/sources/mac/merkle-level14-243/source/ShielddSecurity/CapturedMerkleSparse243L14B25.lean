import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0045
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B25
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 348).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9482 16
def localParent : Nat → Option Row
 | 9482 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 122),[(32220,1)]⟩
 | 9483 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 123),[(32221,1)]⟩
 | 9484 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 124),[(32223,1)]⟩
 | 9485 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 125),[(32222,4),(32223,1)]⟩
 | 9486 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 126),[(32224,1)]⟩
 | 9487 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 127),[(32225,1)]⟩
 | 9488 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 128),[(32227,1)]⟩
 | 9489 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 129),[(32226,4),(32227,1)]⟩
 | 9490 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 130),[(32228,1)]⟩
 | 9491 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 131),[(32229,1)]⟩
 | 9492 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 132),[(32231,1)]⟩
 | 9493 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 133),[(32230,4),(32231,1)]⟩
 | 9494 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 134),[(32232,1)]⟩
 | 9495 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 135),[(32233,1)]⟩
 | 9496 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 136),[(32235,1)]⟩
 | 9497 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 137),[(32234,4),(32235,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B25

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B25.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B25.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B25.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B25.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B25.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B25.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B25.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B25.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B25.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B25.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B25.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B25.count
