import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0012
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistrySparse244G24
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 340).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row)
def indices : List Nat := List.range' 2690 16
def localParent : Nat → Option Row
 | 2690 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 76),[(25428,1)]⟩
 | 2691 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 77),[(25429,1)]⟩
 | 2692 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 78),[(25431,1)]⟩
 | 2693 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 79),[(25430,4),(25431,1)]⟩
 | 2694 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 80),[(25432,1)]⟩
 | 2695 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 81),[(25433,1)]⟩
 | 2696 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 82),[(25435,1)]⟩
 | 2697 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 83),[(25434,4),(25435,1)]⟩
 | 2698 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 84),[(25436,1)]⟩
 | 2699 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 85),[(25437,1)]⟩
 | 2700 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 86),[(25439,1)]⟩
 | 2701 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 87),[(25438,4),(25439,1)]⟩
 | 2702 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 88),[(25440,1)]⟩
 | 2703 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 89),[(25441,1)]⟩
 | 2704 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 90),[(25443,1)]⟩
 | 2705 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 91),[(25442,4),(25443,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedRegistrySparse244G24

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G24.rows
#print axioms ShielddSecurity.CapturedRegistrySparse244G24.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G24.indices
#print axioms ShielddSecurity.CapturedRegistrySparse244G24.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G24.localParent
#print axioms ShielddSecurity.CapturedRegistrySparse244G24.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G24.localCheck
#print axioms ShielddSecurity.CapturedRegistrySparse244G24.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G24.local_checked
#print axioms ShielddSecurity.CapturedRegistrySparse244G24.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G24.count
#print axioms ShielddSecurity.CapturedRegistrySparse244G24.count
