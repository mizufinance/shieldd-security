import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0036
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B17
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 220).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7658 16
def localParent : Nat → Option Row
 | 7658 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 78),[(30396,1)]⟩
 | 7659 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 79),[(30397,1)]⟩
 | 7660 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 80),[(30399,1)]⟩
 | 7661 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 81),[(30398,4),(30399,1)]⟩
 | 7662 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 82),[(30400,1)]⟩
 | 7663 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 83),[(30401,1)]⟩
 | 7664 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 84),[(30403,1)]⟩
 | 7665 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 85),[(30402,4),(30403,1)]⟩
 | 7666 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 86),[(30404,1)]⟩
 | 7667 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 87),[(30405,1)]⟩
 | 7668 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 88),[(30407,1)]⟩
 | 7669 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 89),[(30406,4),(30407,1)]⟩
 | 7670 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 90),[(30408,1)]⟩
 | 7671 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 91),[(30409,1)]⟩
 | 7672 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 92),[(30411,1)]⟩
 | 7673 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 93),[(30410,4),(30411,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B17

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B17.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B17.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B17.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B17.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B17.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B17.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B17.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B17.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B17.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B17.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B17.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B17.count
