import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0038
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L11B13
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 156).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5512)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8018 16
def localParent : Nat → Option Row
 | 8018 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 32),[(30756,1)]⟩
 | 8019 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 33),[(30757,1)]⟩
 | 8020 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 34),[(30759,1)]⟩
 | 8021 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 35),[(30758,4),(30759,1)]⟩
 | 8022 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 36),[(30760,1)]⟩
 | 8023 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 37),[(30761,1)]⟩
 | 8024 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 38),[(30763,1)]⟩
 | 8025 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 39),[(30762,4),(30763,1)]⟩
 | 8026 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 40),[(30764,1)]⟩
 | 8027 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 41),[(30765,1)]⟩
 | 8028 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 42),[(30767,1)]⟩
 | 8029 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 43),[(30766,4),(30767,1)]⟩
 | 8030 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 44),[(30768,1)]⟩
 | 8031 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 45),[(30769,1)]⟩
 | 8032 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 46),[(30771,1)]⟩
 | 8033 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 47),[(30770,4),(30771,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L11B13

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B13.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B13.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B13.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B13.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B13.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B13.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B13.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B13.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B13.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B13.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B13.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B13.count
