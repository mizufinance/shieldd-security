import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0036
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B13
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 156).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7594 16
def localParent : Nat → Option Row
 | 7594 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 14),[(30332,1)]⟩
 | 7595 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 15),[(30333,1)]⟩
 | 7596 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 16),[(30335,1)]⟩
 | 7597 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 17),[(30334,4),(30335,1)]⟩
 | 7598 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 18),[(30336,1)]⟩
 | 7599 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 19),[(30337,1)]⟩
 | 7600 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 20),[(30339,1)]⟩
 | 7601 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 21),[(30338,4),(30339,1)]⟩
 | 7602 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 22),[(30340,1)]⟩
 | 7603 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 23),[(30341,1)]⟩
 | 7604 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 24),[(30343,1)]⟩
 | 7605 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 25),[(30342,4),(30343,1)]⟩
 | 7606 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 26),[(30344,1)]⟩
 | 7607 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 27),[(30345,1)]⟩
 | 7608 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 28),[(30347,1)]⟩
 | 7609 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 29),[(30346,4),(30347,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B13

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B13.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B13.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B13.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B13.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B13.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B13.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B13.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B13.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B13.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B13.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B13.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B13.count
