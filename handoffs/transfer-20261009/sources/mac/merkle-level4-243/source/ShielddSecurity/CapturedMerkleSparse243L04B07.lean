import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0023
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B07
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 60).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4954 16
def localParent : Nat → Option Row
 | 4954 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 90),[(27692,1)]⟩
 | 4955 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 91),[(27693,1)]⟩
 | 4956 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 92),[(27695,1)]⟩
 | 4957 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 93),[(27694,4),(27695,1)]⟩
 | 4958 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 94),[(27696,1)]⟩
 | 4959 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 95),[(27697,1)]⟩
 | 4960 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 96),[(27699,1)]⟩
 | 4961 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 97),[(27698,4),(27699,1)]⟩
 | 4962 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 98),[(27700,1)]⟩
 | 4963 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 99),[(27701,1)]⟩
 | 4964 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 100),[(27703,1)]⟩
 | 4965 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 101),[(27702,4),(27703,1)]⟩
 | 4966 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 102),[(27704,1)]⟩
 | 4967 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 103),[(27705,1)]⟩
 | 4968 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 104),[(27707,1)]⟩
 | 4969 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 105),[(27706,4),(27707,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B07

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B07.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B07.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B07.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B07.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B07.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B07.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B07.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B07.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B07.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B07.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B07.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B07.count
