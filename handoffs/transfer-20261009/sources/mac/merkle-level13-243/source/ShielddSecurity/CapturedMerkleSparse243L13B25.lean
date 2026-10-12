import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0043
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B25
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 348).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9058 16
def localParent : Nat → Option Row
 | 9058 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 114),[(31796,1)]⟩
 | 9059 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 115),[(31797,1)]⟩
 | 9060 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 116),[(31799,1)]⟩
 | 9061 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 117),[(31798,4),(31799,1)]⟩
 | 9062 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 118),[(31800,1)]⟩
 | 9063 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 119),[(31801,1)]⟩
 | 9064 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 120),[(31803,1)]⟩
 | 9065 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 121),[(31802,4),(31803,1)]⟩
 | 9066 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 122),[(31804,1)]⟩
 | 9067 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 123),[(31805,1)]⟩
 | 9068 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 124),[(31807,1)]⟩
 | 9069 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 125),[(31806,4),(31807,1)]⟩
 | 9070 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 126),[(31808,1)]⟩
 | 9071 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 127),[(31809,1)]⟩
 | 9072 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 128),[(31811,1)]⟩
 | 9073 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 129),[(31810,4),(31811,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B25

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B25.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B25.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B25.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B25.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B25.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B25.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B25.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B25.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B25.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B25.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B25.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B25.count
