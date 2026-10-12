import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0018
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L01B25
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 348).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1272)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3970 16
def localParent : Nat → Option Row
 | 3970 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 108),[(26708,1)]⟩
 | 3971 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 109),[(26709,1)]⟩
 | 3972 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 110),[(26711,1)]⟩
 | 3973 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 111),[(26710,4),(26711,1)]⟩
 | 3974 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 112),[(26712,1)]⟩
 | 3975 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 113),[(26713,1)]⟩
 | 3976 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 114),[(26715,1)]⟩
 | 3977 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 115),[(26714,4),(26715,1)]⟩
 | 3978 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 116),[(26716,1)]⟩
 | 3979 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 117),[(26717,1)]⟩
 | 3980 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 118),[(26719,1)]⟩
 | 3981 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 119),[(26718,4),(26719,1)]⟩
 | 3982 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 120),[(26720,1)]⟩
 | 3983 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 121),[(26721,1)]⟩
 | 3984 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 122),[(26723,1)]⟩
 | 3985 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 123),[(26722,4),(26723,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L01B25

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B25.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B25.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B25.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B25.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B25.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B25.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B25.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B25.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B25.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B25.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B25.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B25.count
