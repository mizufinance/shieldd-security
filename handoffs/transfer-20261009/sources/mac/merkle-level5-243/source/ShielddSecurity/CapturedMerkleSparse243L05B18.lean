import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0026
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B18
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 236).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5554 16
def localParent : Nat → Option Row
 | 5554 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 32),[(28292,1)]⟩
 | 5555 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 33),[(28293,1)]⟩
 | 5556 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 34),[(28295,1)]⟩
 | 5557 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 35),[(28294,4),(28295,1)]⟩
 | 5558 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 36),[(28296,1)]⟩
 | 5559 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 37),[(28297,1)]⟩
 | 5560 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 38),[(28299,1)]⟩
 | 5561 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 39),[(28298,4),(28299,1)]⟩
 | 5562 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 40),[(28300,1)]⟩
 | 5563 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 41),[(28301,1)]⟩
 | 5564 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 42),[(28303,1)]⟩
 | 5565 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 43),[(28302,4),(28303,1)]⟩
 | 5566 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 44),[(28304,1)]⟩
 | 5567 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 45),[(28305,1)]⟩
 | 5568 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 46),[(28307,1)]⟩
 | 5569 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 47),[(28306,4),(28307,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B18

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B18.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B18.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B18.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B18.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B18.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B18.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B18.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B18.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B18.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B18.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B18.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B18.count
