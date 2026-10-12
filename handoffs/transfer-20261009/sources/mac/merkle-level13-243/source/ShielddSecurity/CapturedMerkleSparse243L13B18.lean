import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0043
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B18
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 236).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8946 16
def localParent : Nat → Option Row
 | 8946 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 2),[(31684,1)]⟩
 | 8947 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 3),[(31685,1)]⟩
 | 8948 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 4),[(31687,1)]⟩
 | 8949 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 5),[(31686,4),(31687,1)]⟩
 | 8950 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 6),[(31688,1)]⟩
 | 8951 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 7),[(31689,1)]⟩
 | 8952 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 8),[(31691,1)]⟩
 | 8953 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 9),[(31690,4),(31691,1)]⟩
 | 8954 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 10),[(31692,1)]⟩
 | 8955 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 11),[(31693,1)]⟩
 | 8956 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 12),[(31695,1)]⟩
 | 8957 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 13),[(31694,4),(31695,1)]⟩
 | 8958 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 14),[(31696,1)]⟩
 | 8959 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 15),[(31697,1)]⟩
 | 8960 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 16),[(31699,1)]⟩
 | 8961 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 17),[(31698,4),(31699,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B18

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B18.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B18.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B18.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B18.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B18.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B18.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B18.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B18.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B18.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B18.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B18.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B18.count
