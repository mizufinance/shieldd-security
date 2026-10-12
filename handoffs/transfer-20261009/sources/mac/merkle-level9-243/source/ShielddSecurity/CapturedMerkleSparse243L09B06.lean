import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0033
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L09B06
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 44).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4664)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7058 16
def localParent : Nat → Option Row
 | 7058 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 194),[(29796,1)]⟩
 | 7059 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 195),[(29797,1)]⟩
 | 7060 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 196),[(29799,1)]⟩
 | 7061 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 197),[(29798,4),(29799,1)]⟩
 | 7062 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 198),[(29800,1)]⟩
 | 7063 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 199),[(29801,1)]⟩
 | 7064 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 200),[(29803,1)]⟩
 | 7065 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 201),[(29802,4),(29803,1)]⟩
 | 7066 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 202),[(29804,1)]⟩
 | 7067 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 203),[(29805,1)]⟩
 | 7068 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 204),[(29807,1)]⟩
 | 7069 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 205),[(29806,4),(29807,1)]⟩
 | 7070 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 206),[(29808,1)]⟩
 | 7071 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 207),[(29809,1)]⟩
 | 7072 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 208),[(29811,1)]⟩
 | 7073 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 209),[(29810,4),(29811,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L09B06

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B06.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B06.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B06.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B06.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B06.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B06.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B06.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B06.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B06.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B06.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B06.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B06.count
