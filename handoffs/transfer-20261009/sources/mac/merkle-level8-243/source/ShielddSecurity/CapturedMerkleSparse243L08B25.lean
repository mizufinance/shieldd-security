import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0033
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B25
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 348).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6938 16
def localParent : Nat → Option Row
 | 6938 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 74),[(29676,1)]⟩
 | 6939 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 75),[(29677,1)]⟩
 | 6940 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 76),[(29679,1)]⟩
 | 6941 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 77),[(29678,4),(29679,1)]⟩
 | 6942 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 78),[(29680,1)]⟩
 | 6943 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 79),[(29681,1)]⟩
 | 6944 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 80),[(29683,1)]⟩
 | 6945 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 81),[(29682,4),(29683,1)]⟩
 | 6946 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 82),[(29684,1)]⟩
 | 6947 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 83),[(29685,1)]⟩
 | 6948 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 84),[(29687,1)]⟩
 | 6949 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 85),[(29686,4),(29687,1)]⟩
 | 6950 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 86),[(29688,1)]⟩
 | 6951 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 87),[(29689,1)]⟩
 | 6952 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 88),[(29691,1)]⟩
 | 6953 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 89),[(29690,4),(29691,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B25

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B25.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B25.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B25.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B25.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B25.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B25.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B25.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B25.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B25.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B25.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B25.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B25.count
