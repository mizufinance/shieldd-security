import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0021
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B14
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 172).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4642 16
def localParent : Nat → Option Row
 | 4642 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 140),[(27380,1)]⟩
 | 4643 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 141),[(27381,1)]⟩
 | 4644 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 142),[(27383,1)]⟩
 | 4645 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 143),[(27382,4),(27383,1)]⟩
 | 4646 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 144),[(27384,1)]⟩
 | 4647 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 145),[(27385,1)]⟩
 | 4648 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 146),[(27387,1)]⟩
 | 4649 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 147),[(27386,4),(27387,1)]⟩
 | 4650 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 148),[(27388,1)]⟩
 | 4651 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 149),[(27389,1)]⟩
 | 4652 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 150),[(27391,1)]⟩
 | 4653 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 151),[(27390,4),(27391,1)]⟩
 | 4654 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 152),[(27392,1)]⟩
 | 4655 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 153),[(27393,1)]⟩
 | 4656 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 154),[(27395,1)]⟩
 | 4657 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 155),[(27394,4),(27395,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B14

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B14.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B14.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B14.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B14.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B14.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B14.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B14.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B14.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B14.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B14.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B14.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B14.count
