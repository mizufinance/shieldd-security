import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0017
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L01B15
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 188).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1272)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3810 16
def localParent : Nat → Option Row
 | 3810 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 86),[(26548,1)]⟩
 | 3811 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 87),[(26549,1)]⟩
 | 3812 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 88),[(26551,1)]⟩
 | 3813 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 89),[(26550,4),(26551,1)]⟩
 | 3814 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 90),[(26552,1)]⟩
 | 3815 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 91),[(26553,1)]⟩
 | 3816 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 92),[(26555,1)]⟩
 | 3817 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 93),[(26554,4),(26555,1)]⟩
 | 3818 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 94),[(26556,1)]⟩
 | 3819 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 95),[(26557,1)]⟩
 | 3820 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 96),[(26559,1)]⟩
 | 3821 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 97),[(26558,4),(26559,1)]⟩
 | 3822 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 98),[(26560,1)]⟩
 | 3823 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 99),[(26561,1)]⟩
 | 3824 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 100),[(26563,1)]⟩
 | 3825 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 101),[(26562,4),(26563,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L01B15

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B15.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B15.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B15.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B15.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B15.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B15.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B15.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B15.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B15.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B15.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B15.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B15.count
