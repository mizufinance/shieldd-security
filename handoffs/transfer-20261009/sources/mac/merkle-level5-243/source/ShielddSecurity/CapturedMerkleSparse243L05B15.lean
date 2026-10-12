import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0025
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B15
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 188).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5506 16
def localParent : Nat → Option Row
 | 5506 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 286),[(28244,1)]⟩
 | 5507 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 287),[(28245,1)]⟩
 | 5508 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 288),[(28247,1)]⟩
 | 5509 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 289),[(28246,4),(28247,1)]⟩
 | 5510 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 290),[(28248,1)]⟩
 | 5511 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 291),[(28249,1)]⟩
 | 5512 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 292),[(28251,1)]⟩
 | 5513 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 293),[(28250,4),(28251,1)]⟩
 | 5514 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 294),[(28252,1)]⟩
 | 5515 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 295),[(28253,1)]⟩
 | 5516 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 296),[(28255,1)]⟩
 | 5517 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 297),[(28254,4),(28255,1)]⟩
 | 5518 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 298),[(28256,1)]⟩
 | 5519 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 299),[(28257,1)]⟩
 | 5520 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 300),[(28259,1)]⟩
 | 5521 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 301),[(28258,4),(28259,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B15

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B15.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B15.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B15.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B15.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B15.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B15.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B15.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B15.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B15.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B15.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B15.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B15.count
