import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0045
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B26
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 364).take 8).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9498 8
def localParent : Nat → Option Row
 | 9498 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 138),[(32236,1)]⟩
 | 9499 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 139),[(32237,1)]⟩
 | 9500 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 140),[(32239,1)]⟩
 | 9501 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 141),[(32238,4),(32239,1)]⟩
 | 9502 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 142),[(32240,1)]⟩
 | 9503 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 143),[(32241,1)]⟩
 | 9504 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 144),[(32243,1)]⟩
 | 9505 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 145),[(32242,4),(32243,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=8 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B26

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B26.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B26.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B26.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B26.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B26.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B26.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B26.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B26.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B26.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B26.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B26.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B26.count
