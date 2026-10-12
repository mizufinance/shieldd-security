import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0012
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistrySparse244G25
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 356).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row)
def indices : List Nat := List.range' 2706 16
def localParent : Nat → Option Row
 | 2706 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 92),[(25444,1)]⟩
 | 2707 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 93),[(25445,1)]⟩
 | 2708 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 94),[(25447,1)]⟩
 | 2709 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 95),[(25446,4),(25447,1)]⟩
 | 2710 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 96),[(25448,1)]⟩
 | 2711 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 97),[(25449,1)]⟩
 | 2712 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 98),[(25451,1)]⟩
 | 2713 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 99),[(25450,4),(25451,1)]⟩
 | 2714 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 100),[(25452,1)]⟩
 | 2715 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 101),[(25453,1)]⟩
 | 2716 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 102),[(25455,1)]⟩
 | 2717 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 103),[(25454,4),(25455,1)]⟩
 | 2718 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 104),[(25456,1)]⟩
 | 2719 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 105),[(25457,1)]⟩
 | 2720 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 106),[(25459,1)]⟩
 | 2721 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 107),[(25458,4),(25459,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedRegistrySparse244G25

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G25.rows
#print axioms ShielddSecurity.CapturedRegistrySparse244G25.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G25.indices
#print axioms ShielddSecurity.CapturedRegistrySparse244G25.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G25.localParent
#print axioms ShielddSecurity.CapturedRegistrySparse244G25.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G25.localCheck
#print axioms ShielddSecurity.CapturedRegistrySparse244G25.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G25.local_checked
#print axioms ShielddSecurity.CapturedRegistrySparse244G25.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G25.count
#print axioms ShielddSecurity.CapturedRegistrySparse244G25.count
