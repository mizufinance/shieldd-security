import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0018
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B07
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 60).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4106 16
def localParent : Nat → Option Row
 | 4106 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 244),[(26844,1)]⟩
 | 4107 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 245),[(26845,1)]⟩
 | 4108 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 246),[(26847,1)]⟩
 | 4109 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 247),[(26846,4),(26847,1)]⟩
 | 4110 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 248),[(26848,1)]⟩
 | 4111 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 249),[(26849,1)]⟩
 | 4112 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 250),[(26851,1)]⟩
 | 4113 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 251),[(26850,4),(26851,1)]⟩
 | 4114 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 252),[(26852,1)]⟩
 | 4115 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 253),[(26853,1)]⟩
 | 4116 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 254),[(26855,1)]⟩
 | 4117 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 255),[(26854,4),(26855,1)]⟩
 | 4118 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 256),[(26856,1)]⟩
 | 4119 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 257),[(26857,1)]⟩
 | 4120 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 258),[(26859,1)]⟩
 | 4121 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 259),[(26858,4),(26859,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B07

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B07.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B07.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B07.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B07.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B07.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B07.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B07.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B07.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B07.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B07.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B07.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B07.count
