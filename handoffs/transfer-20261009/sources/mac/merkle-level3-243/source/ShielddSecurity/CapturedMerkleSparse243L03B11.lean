import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0021
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B11
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 124).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4594 16
def localParent : Nat → Option Row
 | 4594 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 92),[(27332,1)]⟩
 | 4595 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 93),[(27333,1)]⟩
 | 4596 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 94),[(27335,1)]⟩
 | 4597 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 95),[(27334,4),(27335,1)]⟩
 | 4598 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 96),[(27336,1)]⟩
 | 4599 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 97),[(27337,1)]⟩
 | 4600 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 98),[(27339,1)]⟩
 | 4601 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 99),[(27338,4),(27339,1)]⟩
 | 4602 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 100),[(27340,1)]⟩
 | 4603 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 101),[(27341,1)]⟩
 | 4604 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 102),[(27343,1)]⟩
 | 4605 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 103),[(27342,4),(27343,1)]⟩
 | 4606 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 104),[(27344,1)]⟩
 | 4607 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 105),[(27345,1)]⟩
 | 4608 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 106),[(27347,1)]⟩
 | 4609 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 107),[(27346,4),(27347,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B11

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B11.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B11.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B11.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B11.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B11.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B11.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B11.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B11.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B11.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B11.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B11.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B11.count
