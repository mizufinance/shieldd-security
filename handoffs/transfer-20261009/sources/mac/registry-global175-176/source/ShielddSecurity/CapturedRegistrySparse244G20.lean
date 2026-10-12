import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0012
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistrySparse244G20
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 276).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row)
def indices : List Nat := List.range' 2626 16
def localParent : Nat → Option Row
 | 2626 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 12),[(25364,1)]⟩
 | 2627 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 13),[(25365,1)]⟩
 | 2628 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 14),[(25367,1)]⟩
 | 2629 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 15),[(25366,4),(25367,1)]⟩
 | 2630 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 16),[(25368,1)]⟩
 | 2631 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 17),[(25369,1)]⟩
 | 2632 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 18),[(25371,1)]⟩
 | 2633 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 19),[(25370,4),(25371,1)]⟩
 | 2634 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 20),[(25372,1)]⟩
 | 2635 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 21),[(25373,1)]⟩
 | 2636 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 22),[(25375,1)]⟩
 | 2637 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 23),[(25374,4),(25375,1)]⟩
 | 2638 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 24),[(25376,1)]⟩
 | 2639 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 25),[(25377,1)]⟩
 | 2640 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 26),[(25379,1)]⟩
 | 2641 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 27),[(25378,4),(25379,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedRegistrySparse244G20

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G20.rows
#print axioms ShielddSecurity.CapturedRegistrySparse244G20.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G20.indices
#print axioms ShielddSecurity.CapturedRegistrySparse244G20.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G20.localParent
#print axioms ShielddSecurity.CapturedRegistrySparse244G20.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G20.localCheck
#print axioms ShielddSecurity.CapturedRegistrySparse244G20.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G20.local_checked
#print axioms ShielddSecurity.CapturedRegistrySparse244G20.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G20.count
#print axioms ShielddSecurity.CapturedRegistrySparse244G20.count
