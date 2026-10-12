import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0039
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L11B20
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 268).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5512)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8130 16
def localParent : Nat → Option Row
 | 8130 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 18),[(30868,1)]⟩
 | 8131 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 19),[(30869,1)]⟩
 | 8132 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 20),[(30871,1)]⟩
 | 8133 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 21),[(30870,4),(30871,1)]⟩
 | 8134 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 22),[(30872,1)]⟩
 | 8135 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 23),[(30873,1)]⟩
 | 8136 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 24),[(30875,1)]⟩
 | 8137 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 25),[(30874,4),(30875,1)]⟩
 | 8138 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 26),[(30876,1)]⟩
 | 8139 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 27),[(30877,1)]⟩
 | 8140 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 28),[(30879,1)]⟩
 | 8141 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 29),[(30878,4),(30879,1)]⟩
 | 8142 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 30),[(30880,1)]⟩
 | 8143 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 31),[(30881,1)]⟩
 | 8144 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 32),[(30883,1)]⟩
 | 8145 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 33),[(30882,4),(30883,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L11B20

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B20.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B20.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B20.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B20.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B20.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B20.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B20.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B20.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B20.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B20.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B20.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B20.count
