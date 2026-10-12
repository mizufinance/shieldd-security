import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0045
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B21
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 284).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9418 16
def localParent : Nat → Option Row
 | 9418 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 58),[(32156,1)]⟩
 | 9419 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 59),[(32157,1)]⟩
 | 9420 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 60),[(32159,1)]⟩
 | 9421 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 61),[(32158,4),(32159,1)]⟩
 | 9422 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 62),[(32160,1)]⟩
 | 9423 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 63),[(32161,1)]⟩
 | 9424 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 64),[(32163,1)]⟩
 | 9425 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 65),[(32162,4),(32163,1)]⟩
 | 9426 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 66),[(32164,1)]⟩
 | 9427 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 67),[(32165,1)]⟩
 | 9428 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 68),[(32167,1)]⟩
 | 9429 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 69),[(32166,4),(32167,1)]⟩
 | 9430 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 70),[(32168,1)]⟩
 | 9431 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 71),[(32169,1)]⟩
 | 9432 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 72),[(32171,1)]⟩
 | 9433 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 73),[(32170,4),(32171,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B21

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B21.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B21.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B21.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B21.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B21.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B21.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B21.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B21.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B21.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B21.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B21.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B21.count
