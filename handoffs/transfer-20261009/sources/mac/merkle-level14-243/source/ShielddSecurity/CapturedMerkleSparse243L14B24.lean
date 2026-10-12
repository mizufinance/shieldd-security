import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0045
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B24
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 332).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9466 16
def localParent : Nat → Option Row
 | 9466 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 106),[(32204,1)]⟩
 | 9467 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 107),[(32205,1)]⟩
 | 9468 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 108),[(32207,1)]⟩
 | 9469 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 109),[(32206,4),(32207,1)]⟩
 | 9470 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 110),[(32208,1)]⟩
 | 9471 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 111),[(32209,1)]⟩
 | 9472 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 112),[(32211,1)]⟩
 | 9473 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 113),[(32210,4),(32211,1)]⟩
 | 9474 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 114),[(32212,1)]⟩
 | 9475 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 115),[(32213,1)]⟩
 | 9476 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 116),[(32215,1)]⟩
 | 9477 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 117),[(32214,4),(32215,1)]⟩
 | 9478 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 118),[(32216,1)]⟩
 | 9479 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 119),[(32217,1)]⟩
 | 9480 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 120),[(32219,1)]⟩
 | 9481 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 121),[(32218,4),(32219,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B24

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B24.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B24.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B24.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B24.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B24.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B24.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B24.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B24.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B24.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B24.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B24.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B24.count
