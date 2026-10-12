import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0017
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L01B10
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 108).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1272)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3730 16
def localParent : Nat → Option Row
 | 3730 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 6),[(26468,1)]⟩
 | 3731 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 7),[(26469,1)]⟩
 | 3732 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 8),[(26471,1)]⟩
 | 3733 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 9),[(26470,4),(26471,1)]⟩
 | 3734 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 10),[(26472,1)]⟩
 | 3735 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 11),[(26473,1)]⟩
 | 3736 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 12),[(26475,1)]⟩
 | 3737 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 13),[(26474,4),(26475,1)]⟩
 | 3738 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 14),[(26476,1)]⟩
 | 3739 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 15),[(26477,1)]⟩
 | 3740 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 16),[(26479,1)]⟩
 | 3741 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 17),[(26478,4),(26479,1)]⟩
 | 3742 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 18),[(26480,1)]⟩
 | 3743 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 19),[(26481,1)]⟩
 | 3744 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 20),[(26483,1)]⟩
 | 3745 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 21),[(26482,4),(26483,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L01B10

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B10.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B10.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B10.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B10.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B10.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B10.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B10.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B10.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B10.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B10.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B10.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B10.count
