import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0017
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L01B17
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 220).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1272)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3842 16
def localParent : Nat → Option Row
 | 3842 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 118),[(26580,1)]⟩
 | 3843 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 119),[(26581,1)]⟩
 | 3844 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 120),[(26583,1)]⟩
 | 3845 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 121),[(26582,4),(26583,1)]⟩
 | 3846 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 122),[(26584,1)]⟩
 | 3847 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 123),[(26585,1)]⟩
 | 3848 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 124),[(26587,1)]⟩
 | 3849 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 125),[(26586,4),(26587,1)]⟩
 | 3850 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 126),[(26588,1)]⟩
 | 3851 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 127),[(26589,1)]⟩
 | 3852 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 128),[(26591,1)]⟩
 | 3853 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 129),[(26590,4),(26591,1)]⟩
 | 3854 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 130),[(26592,1)]⟩
 | 3855 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 131),[(26593,1)]⟩
 | 3856 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 132),[(26595,1)]⟩
 | 3857 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 133),[(26594,4),(26595,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L01B17

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B17.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B17.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B17.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B17.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B17.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B17.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B17.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B17.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B17.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B17.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B17.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B17.count
