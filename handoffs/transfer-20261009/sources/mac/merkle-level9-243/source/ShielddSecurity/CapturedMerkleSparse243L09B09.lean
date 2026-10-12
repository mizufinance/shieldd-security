import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0033
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L09B09
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 92).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4664)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7106 16
def localParent : Nat → Option Row
 | 7106 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 242),[(29844,1)]⟩
 | 7107 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 243),[(29845,1)]⟩
 | 7108 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 244),[(29847,1)]⟩
 | 7109 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 245),[(29846,4),(29847,1)]⟩
 | 7110 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 246),[(29848,1)]⟩
 | 7111 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 247),[(29849,1)]⟩
 | 7112 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 248),[(29851,1)]⟩
 | 7113 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 249),[(29850,4),(29851,1)]⟩
 | 7114 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 250),[(29852,1)]⟩
 | 7115 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 251),[(29853,1)]⟩
 | 7116 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 252),[(29855,1)]⟩
 | 7117 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 253),[(29854,4),(29855,1)]⟩
 | 7118 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 254),[(29856,1)]⟩
 | 7119 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 255),[(29857,1)]⟩
 | 7120 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 256),[(29859,1)]⟩
 | 7121 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 257),[(29858,4),(29859,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L09B09

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B09.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B09.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B09.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B09.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B09.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B09.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B09.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B09.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B09.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B09.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B09.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B09.count
