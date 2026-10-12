import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0018
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L01B24
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 332).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1272)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3954 16
def localParent : Nat → Option Row
 | 3954 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 92),[(26692,1)]⟩
 | 3955 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 93),[(26693,1)]⟩
 | 3956 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 94),[(26695,1)]⟩
 | 3957 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 95),[(26694,4),(26695,1)]⟩
 | 3958 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 96),[(26696,1)]⟩
 | 3959 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 97),[(26697,1)]⟩
 | 3960 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 98),[(26699,1)]⟩
 | 3961 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 99),[(26698,4),(26699,1)]⟩
 | 3962 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 100),[(26700,1)]⟩
 | 3963 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 101),[(26701,1)]⟩
 | 3964 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 102),[(26703,1)]⟩
 | 3965 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 103),[(26702,4),(26703,1)]⟩
 | 3966 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 104),[(26704,1)]⟩
 | 3967 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 105),[(26705,1)]⟩
 | 3968 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 106),[(26707,1)]⟩
 | 3969 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 107),[(26706,4),(26707,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L01B24

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B24.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B24.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B24.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B24.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B24.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B24.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B24.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B24.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B24.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B24.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B24.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B24.count
