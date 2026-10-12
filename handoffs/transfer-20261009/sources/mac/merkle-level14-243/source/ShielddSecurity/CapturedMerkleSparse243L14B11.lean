import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0044
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B11
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 124).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9258 16
def localParent : Nat → Option Row
 | 9258 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 82),[(31996,1)]⟩
 | 9259 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 83),[(31997,1)]⟩
 | 9260 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 84),[(31999,1)]⟩
 | 9261 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 85),[(31998,4),(31999,1)]⟩
 | 9262 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 86),[(32000,1)]⟩
 | 9263 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 87),[(32001,1)]⟩
 | 9264 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 88),[(32003,1)]⟩
 | 9265 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 89),[(32002,4),(32003,1)]⟩
 | 9266 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 90),[(32004,1)]⟩
 | 9267 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 91),[(32005,1)]⟩
 | 9268 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 92),[(32007,1)]⟩
 | 9269 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 93),[(32006,4),(32007,1)]⟩
 | 9270 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 94),[(32008,1)]⟩
 | 9271 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 95),[(32009,1)]⟩
 | 9272 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 96),[(32011,1)]⟩
 | 9273 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 97),[(32010,4),(32011,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B11

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B11.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B11.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B11.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B11.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B11.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B11.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B11.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B11.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B11.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B11.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B11.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B11.count
