import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0012
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistrySparse244G23
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 324).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row)
def indices : List Nat := List.range' 2674 16
def localParent : Nat → Option Row
 | 2674 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 60),[(25412,1)]⟩
 | 2675 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 61),[(25413,1)]⟩
 | 2676 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 62),[(25415,1)]⟩
 | 2677 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 63),[(25414,4),(25415,1)]⟩
 | 2678 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 64),[(25416,1)]⟩
 | 2679 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 65),[(25417,1)]⟩
 | 2680 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 66),[(25419,1)]⟩
 | 2681 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 67),[(25418,4),(25419,1)]⟩
 | 2682 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 68),[(25420,1)]⟩
 | 2683 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 69),[(25421,1)]⟩
 | 2684 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 70),[(25423,1)]⟩
 | 2685 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 71),[(25422,4),(25423,1)]⟩
 | 2686 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 72),[(25424,1)]⟩
 | 2687 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 73),[(25425,1)]⟩
 | 2688 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 74),[(25427,1)]⟩
 | 2689 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 75),[(25426,4),(25427,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedRegistrySparse244G23

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G23.rows
#print axioms ShielddSecurity.CapturedRegistrySparse244G23.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G23.indices
#print axioms ShielddSecurity.CapturedRegistrySparse244G23.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G23.localParent
#print axioms ShielddSecurity.CapturedRegistrySparse244G23.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G23.localCheck
#print axioms ShielddSecurity.CapturedRegistrySparse244G23.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G23.local_checked
#print axioms ShielddSecurity.CapturedRegistrySparse244G23.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G23.count
#print axioms ShielddSecurity.CapturedRegistrySparse244G23.count
