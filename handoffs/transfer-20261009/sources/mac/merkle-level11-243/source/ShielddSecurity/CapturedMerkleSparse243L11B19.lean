import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0039
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L11B19
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 252).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5512)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8114 16
def localParent : Nat → Option Row
 | 8114 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 2),[(30852,1)]⟩
 | 8115 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 3),[(30853,1)]⟩
 | 8116 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 4),[(30855,1)]⟩
 | 8117 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 5),[(30854,4),(30855,1)]⟩
 | 8118 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 6),[(30856,1)]⟩
 | 8119 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 7),[(30857,1)]⟩
 | 8120 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 8),[(30859,1)]⟩
 | 8121 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 9),[(30858,4),(30859,1)]⟩
 | 8122 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 10),[(30860,1)]⟩
 | 8123 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 11),[(30861,1)]⟩
 | 8124 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 12),[(30863,1)]⟩
 | 8125 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 13),[(30862,4),(30863,1)]⟩
 | 8126 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 14),[(30864,1)]⟩
 | 8127 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 15),[(30865,1)]⟩
 | 8128 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 16),[(30867,1)]⟩
 | 8129 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 17),[(30866,4),(30867,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L11B19

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B19.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B19.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B19.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B19.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B19.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B19.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B19.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B19.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B19.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B19.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B19.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B19.count
