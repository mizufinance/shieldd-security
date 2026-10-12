import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0021
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B16
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 204).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4674 16
def localParent : Nat → Option Row
 | 4674 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 172),[(27412,1)]⟩
 | 4675 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 173),[(27413,1)]⟩
 | 4676 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 174),[(27415,1)]⟩
 | 4677 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 175),[(27414,4),(27415,1)]⟩
 | 4678 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 176),[(27416,1)]⟩
 | 4679 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 177),[(27417,1)]⟩
 | 4680 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 178),[(27419,1)]⟩
 | 4681 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 179),[(27418,4),(27419,1)]⟩
 | 4682 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 180),[(27420,1)]⟩
 | 4683 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 181),[(27421,1)]⟩
 | 4684 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 182),[(27423,1)]⟩
 | 4685 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 183),[(27422,4),(27423,1)]⟩
 | 4686 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 184),[(27424,1)]⟩
 | 4687 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 185),[(27425,1)]⟩
 | 4688 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 186),[(27427,1)]⟩
 | 4689 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 187),[(27426,4),(27427,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B16

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B16.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B16.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B16.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B16.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B16.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B16.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B16.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B16.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B16.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B16.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B16.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B16.count
