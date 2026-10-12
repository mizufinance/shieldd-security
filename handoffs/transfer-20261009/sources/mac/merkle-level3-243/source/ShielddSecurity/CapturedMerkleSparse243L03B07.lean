import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0021
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B07
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 60).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4530 16
def localParent : Nat → Option Row
 | 4530 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 28),[(27268,1)]⟩
 | 4531 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 29),[(27269,1)]⟩
 | 4532 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 30),[(27271,1)]⟩
 | 4533 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 31),[(27270,4),(27271,1)]⟩
 | 4534 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 32),[(27272,1)]⟩
 | 4535 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 33),[(27273,1)]⟩
 | 4536 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 34),[(27275,1)]⟩
 | 4537 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 35),[(27274,4),(27275,1)]⟩
 | 4538 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 36),[(27276,1)]⟩
 | 4539 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 37),[(27277,1)]⟩
 | 4540 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 38),[(27279,1)]⟩
 | 4541 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 39),[(27278,4),(27279,1)]⟩
 | 4542 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 40),[(27280,1)]⟩
 | 4543 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 41),[(27281,1)]⟩
 | 4544 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 42),[(27283,1)]⟩
 | 4545 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 43),[(27282,4),(27283,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B07

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B07.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B07.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B07.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B07.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B07.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B07.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B07.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B07.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B07.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B07.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B07.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B07.count
