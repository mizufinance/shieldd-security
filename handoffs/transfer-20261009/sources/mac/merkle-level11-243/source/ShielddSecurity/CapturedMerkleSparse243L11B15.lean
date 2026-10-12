import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0038
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L11B15
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 188).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5512)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8050 16
def localParent : Nat → Option Row
 | 8050 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 64),[(30788,1)]⟩
 | 8051 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 65),[(30789,1)]⟩
 | 8052 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 66),[(30791,1)]⟩
 | 8053 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 67),[(30790,4),(30791,1)]⟩
 | 8054 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 68),[(30792,1)]⟩
 | 8055 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 69),[(30793,1)]⟩
 | 8056 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 70),[(30795,1)]⟩
 | 8057 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 71),[(30794,4),(30795,1)]⟩
 | 8058 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 72),[(30796,1)]⟩
 | 8059 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 73),[(30797,1)]⟩
 | 8060 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 74),[(30799,1)]⟩
 | 8061 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 75),[(30798,4),(30799,1)]⟩
 | 8062 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 76),[(30800,1)]⟩
 | 8063 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 77),[(30801,1)]⟩
 | 8064 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 78),[(30803,1)]⟩
 | 8065 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 79),[(30802,4),(30803,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L11B15

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B15.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B15.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B15.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B15.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B15.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B15.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B15.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B15.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B15.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B15.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B15.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B15.count
