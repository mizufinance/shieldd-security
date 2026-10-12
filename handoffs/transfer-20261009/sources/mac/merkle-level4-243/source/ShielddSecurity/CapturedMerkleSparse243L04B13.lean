import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0023
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B13
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 156).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5050 16
def localParent : Nat → Option Row
 | 5050 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 186),[(27788,1)]⟩
 | 5051 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 187),[(27789,1)]⟩
 | 5052 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 188),[(27791,1)]⟩
 | 5053 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 189),[(27790,4),(27791,1)]⟩
 | 5054 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 190),[(27792,1)]⟩
 | 5055 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 191),[(27793,1)]⟩
 | 5056 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 192),[(27795,1)]⟩
 | 5057 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 193),[(27794,4),(27795,1)]⟩
 | 5058 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 194),[(27796,1)]⟩
 | 5059 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 195),[(27797,1)]⟩
 | 5060 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 196),[(27799,1)]⟩
 | 5061 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 197),[(27798,4),(27799,1)]⟩
 | 5062 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 198),[(27800,1)]⟩
 | 5063 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 199),[(27801,1)]⟩
 | 5064 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 200),[(27803,1)]⟩
 | 5065 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 201),[(27802,4),(27803,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B13

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B13.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B13.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B13.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B13.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B13.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B13.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B13.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B13.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B13.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B13.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B13.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B13.count
