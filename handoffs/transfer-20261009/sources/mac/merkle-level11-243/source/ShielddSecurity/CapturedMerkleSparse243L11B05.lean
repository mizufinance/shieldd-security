import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0037
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L11B05
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 28).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5512)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7890 16
def localParent : Nat → Option Row
 | 7890 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 194),[(30628,1)]⟩
 | 7891 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 195),[(30629,1)]⟩
 | 7892 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 196),[(30631,1)]⟩
 | 7893 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 197),[(30630,4),(30631,1)]⟩
 | 7894 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 198),[(30632,1)]⟩
 | 7895 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 199),[(30633,1)]⟩
 | 7896 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 200),[(30635,1)]⟩
 | 7897 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 201),[(30634,4),(30635,1)]⟩
 | 7898 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 202),[(30636,1)]⟩
 | 7899 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 203),[(30637,1)]⟩
 | 7900 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 204),[(30639,1)]⟩
 | 7901 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 205),[(30638,4),(30639,1)]⟩
 | 7902 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 206),[(30640,1)]⟩
 | 7903 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 207),[(30641,1)]⟩
 | 7904 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 208),[(30643,1)]⟩
 | 7905 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 209),[(30642,4),(30643,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L11B05

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B05.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B05.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B05.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B05.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B05.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B05.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B05.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B05.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B05.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B05.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B05.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B05.count
