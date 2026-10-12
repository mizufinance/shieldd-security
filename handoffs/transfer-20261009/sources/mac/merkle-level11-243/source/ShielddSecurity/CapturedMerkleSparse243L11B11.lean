import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0038
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L11B11
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 124).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5512)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7986 16
def localParent : Nat → Option Row
 | 7986 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 0),[(30724,1)]⟩
 | 7987 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 1),[(30725,1)]⟩
 | 7988 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 2),[(30727,1)]⟩
 | 7989 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 3),[(30726,4),(30727,1)]⟩
 | 7990 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 4),[(30728,1)]⟩
 | 7991 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 5),[(30729,1)]⟩
 | 7992 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 6),[(30731,1)]⟩
 | 7993 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 7),[(30730,4),(30731,1)]⟩
 | 7994 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 8),[(30732,1)]⟩
 | 7995 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 9),[(30733,1)]⟩
 | 7996 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 10),[(30735,1)]⟩
 | 7997 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 11),[(30734,4),(30735,1)]⟩
 | 7998 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 12),[(30736,1)]⟩
 | 7999 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 13),[(30737,1)]⟩
 | 8000 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 14),[(30739,1)]⟩
 | 8001 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 15),[(30738,4),(30739,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L11B11

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B11.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B11.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B11.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B11.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B11.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B11.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B11.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B11.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B11.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B11.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B11.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B11.count
