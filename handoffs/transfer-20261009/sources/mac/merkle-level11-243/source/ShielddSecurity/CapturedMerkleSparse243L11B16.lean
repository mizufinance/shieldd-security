import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0038
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L11B16
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 204).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5512)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8066 16
def localParent : Nat → Option Row
 | 8066 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 80),[(30804,1)]⟩
 | 8067 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 81),[(30805,1)]⟩
 | 8068 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 82),[(30807,1)]⟩
 | 8069 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 83),[(30806,4),(30807,1)]⟩
 | 8070 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 84),[(30808,1)]⟩
 | 8071 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 85),[(30809,1)]⟩
 | 8072 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 86),[(30811,1)]⟩
 | 8073 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 87),[(30810,4),(30811,1)]⟩
 | 8074 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 88),[(30812,1)]⟩
 | 8075 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 89),[(30813,1)]⟩
 | 8076 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 90),[(30815,1)]⟩
 | 8077 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 91),[(30814,4),(30815,1)]⟩
 | 8078 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 92),[(30816,1)]⟩
 | 8079 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 93),[(30817,1)]⟩
 | 8080 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 94),[(30819,1)]⟩
 | 8081 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 95),[(30818,4),(30819,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L11B16

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B16.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B16.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B16.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B16.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B16.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B16.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B16.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B16.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B16.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B16.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B16.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B16.count
