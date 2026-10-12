import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0018
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L01B26
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 364).take 8).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1272)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3986 8
def localParent : Nat → Option Row
 | 3986 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 124),[(26724,1)]⟩
 | 3987 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 125),[(26725,1)]⟩
 | 3988 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 126),[(26727,1)]⟩
 | 3989 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 127),[(26726,4),(26727,1)]⟩
 | 3990 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 128),[(26728,1)]⟩
 | 3991 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 129),[(26729,1)]⟩
 | 3992 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 130),[(26731,1)]⟩
 | 3993 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 131),[(26730,4),(26731,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=8 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L01B26

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B26.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B26.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B26.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B26.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B26.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B26.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B26.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B26.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B26.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B26.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B26.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B26.count
