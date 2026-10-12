import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0012
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistrySparse244G21
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 292).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row)
def indices : List Nat := List.range' 2642 16
def localParent : Nat → Option Row
 | 2642 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 28),[(25380,1)]⟩
 | 2643 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 29),[(25381,1)]⟩
 | 2644 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 30),[(25383,1)]⟩
 | 2645 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 31),[(25382,4),(25383,1)]⟩
 | 2646 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 32),[(25384,1)]⟩
 | 2647 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 33),[(25385,1)]⟩
 | 2648 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 34),[(25387,1)]⟩
 | 2649 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 35),[(25386,4),(25387,1)]⟩
 | 2650 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 36),[(25388,1)]⟩
 | 2651 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 37),[(25389,1)]⟩
 | 2652 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 38),[(25391,1)]⟩
 | 2653 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 39),[(25390,4),(25391,1)]⟩
 | 2654 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 40),[(25392,1)]⟩
 | 2655 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 41),[(25393,1)]⟩
 | 2656 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 42),[(25395,1)]⟩
 | 2657 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0012.inputs 43),[(25394,4),(25395,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedRegistrySparse244G21

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G21.rows
#print axioms ShielddSecurity.CapturedRegistrySparse244G21.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G21.indices
#print axioms ShielddSecurity.CapturedRegistrySparse244G21.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G21.localParent
#print axioms ShielddSecurity.CapturedRegistrySparse244G21.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G21.localCheck
#print axioms ShielddSecurity.CapturedRegistrySparse244G21.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G21.local_checked
#print axioms ShielddSecurity.CapturedRegistrySparse244G21.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistrySparse244G21.count
#print axioms ShielddSecurity.CapturedRegistrySparse244G21.count
