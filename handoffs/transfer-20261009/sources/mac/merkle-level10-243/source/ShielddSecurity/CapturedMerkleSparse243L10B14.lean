import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0036
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B14
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 172).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7610 16
def localParent : Nat → Option Row
 | 7610 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 30),[(30348,1)]⟩
 | 7611 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 31),[(30349,1)]⟩
 | 7612 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 32),[(30351,1)]⟩
 | 7613 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 33),[(30350,4),(30351,1)]⟩
 | 7614 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 34),[(30352,1)]⟩
 | 7615 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 35),[(30353,1)]⟩
 | 7616 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 36),[(30355,1)]⟩
 | 7617 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 37),[(30354,4),(30355,1)]⟩
 | 7618 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 38),[(30356,1)]⟩
 | 7619 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 39),[(30357,1)]⟩
 | 7620 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 40),[(30359,1)]⟩
 | 7621 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 41),[(30358,4),(30359,1)]⟩
 | 7622 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 42),[(30360,1)]⟩
 | 7623 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 43),[(30361,1)]⟩
 | 7624 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 44),[(30363,1)]⟩
 | 7625 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 45),[(30362,4),(30363,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B14

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B14.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B14.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B14.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B14.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B14.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B14.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B14.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B14.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B14.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B14.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B14.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B14.count
