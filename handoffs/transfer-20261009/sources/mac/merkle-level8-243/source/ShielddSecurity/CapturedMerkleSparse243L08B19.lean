import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0032
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B19
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 252).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6842 16
def localParent : Nat → Option Row
 | 6842 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 82),[(29580,1)]⟩
 | 6843 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 83),[(29581,1)]⟩
 | 6844 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 84),[(29583,1)]⟩
 | 6845 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 85),[(29582,4),(29583,1)]⟩
 | 6846 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 86),[(29584,1)]⟩
 | 6847 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 87),[(29585,1)]⟩
 | 6848 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 88),[(29587,1)]⟩
 | 6849 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 89),[(29586,4),(29587,1)]⟩
 | 6850 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 90),[(29588,1)]⟩
 | 6851 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 91),[(29589,1)]⟩
 | 6852 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 92),[(29591,1)]⟩
 | 6853 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 93),[(29590,4),(29591,1)]⟩
 | 6854 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 94),[(29592,1)]⟩
 | 6855 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 95),[(29593,1)]⟩
 | 6856 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 96),[(29595,1)]⟩
 | 6857 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 97),[(29594,4),(29595,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B19

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B19.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B19.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B19.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B19.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B19.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B19.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B19.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B19.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B19.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B19.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B19.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B19.count
