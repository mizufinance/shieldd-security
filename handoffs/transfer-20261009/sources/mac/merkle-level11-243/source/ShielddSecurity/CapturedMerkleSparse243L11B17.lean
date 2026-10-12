import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0038
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L11B17
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 220).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5512)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8082 16
def localParent : Nat → Option Row
 | 8082 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 96),[(30820,1)]⟩
 | 8083 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 97),[(30821,1)]⟩
 | 8084 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 98),[(30823,1)]⟩
 | 8085 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 99),[(30822,4),(30823,1)]⟩
 | 8086 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 100),[(30824,1)]⟩
 | 8087 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 101),[(30825,1)]⟩
 | 8088 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 102),[(30827,1)]⟩
 | 8089 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 103),[(30826,4),(30827,1)]⟩
 | 8090 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 104),[(30828,1)]⟩
 | 8091 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 105),[(30829,1)]⟩
 | 8092 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 106),[(30831,1)]⟩
 | 8093 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 107),[(30830,4),(30831,1)]⟩
 | 8094 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 108),[(30832,1)]⟩
 | 8095 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 109),[(30833,1)]⟩
 | 8096 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 110),[(30835,1)]⟩
 | 8097 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 111),[(30834,4),(30835,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L11B17

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B17.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B17.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B17.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B17.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B17.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B17.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B17.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B17.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B17.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B17.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B17.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B17.count
