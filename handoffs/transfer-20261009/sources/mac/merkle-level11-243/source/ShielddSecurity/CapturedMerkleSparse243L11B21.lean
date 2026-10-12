import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0039
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L11B21
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 284).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5512)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8146 16
def localParent : Nat → Option Row
 | 8146 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 34),[(30884,1)]⟩
 | 8147 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 35),[(30885,1)]⟩
 | 8148 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 36),[(30887,1)]⟩
 | 8149 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 37),[(30886,4),(30887,1)]⟩
 | 8150 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 38),[(30888,1)]⟩
 | 8151 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 39),[(30889,1)]⟩
 | 8152 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 40),[(30891,1)]⟩
 | 8153 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 41),[(30890,4),(30891,1)]⟩
 | 8154 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 42),[(30892,1)]⟩
 | 8155 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 43),[(30893,1)]⟩
 | 8156 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 44),[(30895,1)]⟩
 | 8157 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 45),[(30894,4),(30895,1)]⟩
 | 8158 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 46),[(30896,1)]⟩
 | 8159 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 47),[(30897,1)]⟩
 | 8160 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 48),[(30899,1)]⟩
 | 8161 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 49),[(30898,4),(30899,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L11B21

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B21.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B21.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B21.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B21.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B21.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B21.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B21.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B21.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B21.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B21.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B21.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B21.count
