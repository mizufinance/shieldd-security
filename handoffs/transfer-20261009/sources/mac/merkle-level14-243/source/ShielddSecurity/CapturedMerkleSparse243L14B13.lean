import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0044
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B13
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 156).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9290 16
def localParent : Nat → Option Row
 | 9290 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 114),[(32028,1)]⟩
 | 9291 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 115),[(32029,1)]⟩
 | 9292 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 116),[(32031,1)]⟩
 | 9293 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 117),[(32030,4),(32031,1)]⟩
 | 9294 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 118),[(32032,1)]⟩
 | 9295 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 119),[(32033,1)]⟩
 | 9296 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 120),[(32035,1)]⟩
 | 9297 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 121),[(32034,4),(32035,1)]⟩
 | 9298 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 122),[(32036,1)]⟩
 | 9299 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 123),[(32037,1)]⟩
 | 9300 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 124),[(32039,1)]⟩
 | 9301 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 125),[(32038,4),(32039,1)]⟩
 | 9302 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 126),[(32040,1)]⟩
 | 9303 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 127),[(32041,1)]⟩
 | 9304 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 128),[(32043,1)]⟩
 | 9305 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 129),[(32042,4),(32043,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B13

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B13.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B13.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B13.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B13.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B13.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B13.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B13.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B13.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B13.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B13.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B13.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B13.count
