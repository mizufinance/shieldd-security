import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0023
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B06
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 44).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4938 16
def localParent : Nat → Option Row
 | 4938 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 74),[(27676,1)]⟩
 | 4939 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 75),[(27677,1)]⟩
 | 4940 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 76),[(27679,1)]⟩
 | 4941 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 77),[(27678,4),(27679,1)]⟩
 | 4942 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 78),[(27680,1)]⟩
 | 4943 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 79),[(27681,1)]⟩
 | 4944 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 80),[(27683,1)]⟩
 | 4945 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 81),[(27682,4),(27683,1)]⟩
 | 4946 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 82),[(27684,1)]⟩
 | 4947 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 83),[(27685,1)]⟩
 | 4948 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 84),[(27687,1)]⟩
 | 4949 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 85),[(27686,4),(27687,1)]⟩
 | 4950 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 86),[(27688,1)]⟩
 | 4951 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 87),[(27689,1)]⟩
 | 4952 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 88),[(27691,1)]⟩
 | 4953 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 89),[(27690,4),(27691,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B06

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B06.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B06.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B06.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B06.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B06.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B06.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B06.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B06.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B06.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B06.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B06.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B06.count
