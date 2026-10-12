import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0037
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L11B08
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 76).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5512)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7938 16
def localParent : Nat → Option Row
 | 7938 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 242),[(30676,1)]⟩
 | 7939 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 243),[(30677,1)]⟩
 | 7940 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 244),[(30679,1)]⟩
 | 7941 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 245),[(30678,4),(30679,1)]⟩
 | 7942 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 246),[(30680,1)]⟩
 | 7943 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 247),[(30681,1)]⟩
 | 7944 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 248),[(30683,1)]⟩
 | 7945 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 249),[(30682,4),(30683,1)]⟩
 | 7946 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 250),[(30684,1)]⟩
 | 7947 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 251),[(30685,1)]⟩
 | 7948 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 252),[(30687,1)]⟩
 | 7949 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 253),[(30686,4),(30687,1)]⟩
 | 7950 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 254),[(30688,1)]⟩
 | 7951 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 255),[(30689,1)]⟩
 | 7952 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 256),[(30691,1)]⟩
 | 7953 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 257),[(30690,4),(30691,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L11B08

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B08.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B08.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B08.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B08.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B08.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B08.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B08.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B08.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B08.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B08.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B08.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B08.count
