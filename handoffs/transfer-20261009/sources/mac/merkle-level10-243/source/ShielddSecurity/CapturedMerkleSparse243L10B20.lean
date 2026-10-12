import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0037
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B20
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 268).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7706 16
def localParent : Nat → Option Row
 | 7706 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 10),[(30444,1)]⟩
 | 7707 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 11),[(30445,1)]⟩
 | 7708 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 12),[(30447,1)]⟩
 | 7709 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 13),[(30446,4),(30447,1)]⟩
 | 7710 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 14),[(30448,1)]⟩
 | 7711 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 15),[(30449,1)]⟩
 | 7712 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 16),[(30451,1)]⟩
 | 7713 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 17),[(30450,4),(30451,1)]⟩
 | 7714 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 18),[(30452,1)]⟩
 | 7715 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 19),[(30453,1)]⟩
 | 7716 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 20),[(30455,1)]⟩
 | 7717 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 21),[(30454,4),(30455,1)]⟩
 | 7718 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 22),[(30456,1)]⟩
 | 7719 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 23),[(30457,1)]⟩
 | 7720 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 24),[(30459,1)]⟩
 | 7721 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 25),[(30458,4),(30459,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B20

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B20.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B20.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B20.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B20.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B20.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B20.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B20.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B20.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B20.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B20.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B20.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B20.count
