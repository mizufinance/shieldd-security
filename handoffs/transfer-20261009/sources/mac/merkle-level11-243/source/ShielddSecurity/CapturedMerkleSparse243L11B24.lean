import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0039
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L11B24
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 332).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5512)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8194 16
def localParent : Nat → Option Row
 | 8194 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 82),[(30932,1)]⟩
 | 8195 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 83),[(30933,1)]⟩
 | 8196 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 84),[(30935,1)]⟩
 | 8197 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 85),[(30934,4),(30935,1)]⟩
 | 8198 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 86),[(30936,1)]⟩
 | 8199 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 87),[(30937,1)]⟩
 | 8200 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 88),[(30939,1)]⟩
 | 8201 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 89),[(30938,4),(30939,1)]⟩
 | 8202 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 90),[(30940,1)]⟩
 | 8203 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 91),[(30941,1)]⟩
 | 8204 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 92),[(30943,1)]⟩
 | 8205 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 93),[(30942,4),(30943,1)]⟩
 | 8206 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 94),[(30944,1)]⟩
 | 8207 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 95),[(30945,1)]⟩
 | 8208 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 96),[(30947,1)]⟩
 | 8209 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 97),[(30946,4),(30947,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L11B24

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B24.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B24.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B24.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B24.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B24.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B24.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B24.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B24.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B24.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B24.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B24.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B24.count
