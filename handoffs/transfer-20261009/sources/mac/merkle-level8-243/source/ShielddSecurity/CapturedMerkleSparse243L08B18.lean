import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0032
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B18
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 236).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6826 16
def localParent : Nat → Option Row
 | 6826 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 66),[(29564,1)]⟩
 | 6827 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 67),[(29565,1)]⟩
 | 6828 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 68),[(29567,1)]⟩
 | 6829 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 69),[(29566,4),(29567,1)]⟩
 | 6830 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 70),[(29568,1)]⟩
 | 6831 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 71),[(29569,1)]⟩
 | 6832 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 72),[(29571,1)]⟩
 | 6833 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 73),[(29570,4),(29571,1)]⟩
 | 6834 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 74),[(29572,1)]⟩
 | 6835 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 75),[(29573,1)]⟩
 | 6836 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 76),[(29575,1)]⟩
 | 6837 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 77),[(29574,4),(29575,1)]⟩
 | 6838 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 78),[(29576,1)]⟩
 | 6839 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 79),[(29577,1)]⟩
 | 6840 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 80),[(29579,1)]⟩
 | 6841 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 81),[(29578,4),(29579,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B18

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B18.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B18.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B18.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B18.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B18.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B18.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B18.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B18.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B18.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B18.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B18.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B18.count
