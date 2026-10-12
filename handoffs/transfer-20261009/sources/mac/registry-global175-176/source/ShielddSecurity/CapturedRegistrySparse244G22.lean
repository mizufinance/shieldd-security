import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0012
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistrySparse244G22
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 308).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row)
def indices : List Nat := List.range' 2658 16
def localParent : Nat → Option Row
 | 2658 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 44),[(25396,1)]⟩
 | 2659 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 45),[(25397,1)]⟩
 | 2660 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 46),[(25399,1)]⟩
 | 2661 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 47),[(25398,4),(25399,1)]⟩
 | 2662 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 48),[(25400,1)]⟩
 | 2663 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 49),[(25401,1)]⟩
 | 2664 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 50),[(25403,1)]⟩
 | 2665 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 51),[(25402,4),(25403,1)]⟩
 | 2666 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 52),[(25404,1)]⟩
 | 2667 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 53),[(25405,1)]⟩
 | 2668 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 54),[(25407,1)]⟩
 | 2669 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 55),[(25406,4),(25407,1)]⟩
 | 2670 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 56),[(25408,1)]⟩
 | 2671 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 57),[(25409,1)]⟩
 | 2672 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 58),[(25411,1)]⟩
 | 2673 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 59),[(25410,4),(25411,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedRegistrySparse244G22

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G22.rows
#print axioms ShielddSecurity.CapturedRegistrySparse244G22.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G22.indices
#print axioms ShielddSecurity.CapturedRegistrySparse244G22.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G22.localParent
#print axioms ShielddSecurity.CapturedRegistrySparse244G22.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G22.localCheck
#print axioms ShielddSecurity.CapturedRegistrySparse244G22.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G22.local_checked
#print axioms ShielddSecurity.CapturedRegistrySparse244G22.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G22.count
#print axioms ShielddSecurity.CapturedRegistrySparse244G22.count
