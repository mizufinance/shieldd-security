import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0036
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B18
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 236).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7674 16
def localParent : Nat → Option Row
 | 7674 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 94),[(30412,1)]⟩
 | 7675 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 95),[(30413,1)]⟩
 | 7676 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 96),[(30415,1)]⟩
 | 7677 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 97),[(30414,4),(30415,1)]⟩
 | 7678 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 98),[(30416,1)]⟩
 | 7679 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 99),[(30417,1)]⟩
 | 7680 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 100),[(30419,1)]⟩
 | 7681 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 101),[(30418,4),(30419,1)]⟩
 | 7682 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 102),[(30420,1)]⟩
 | 7683 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 103),[(30421,1)]⟩
 | 7684 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 104),[(30423,1)]⟩
 | 7685 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 105),[(30422,4),(30423,1)]⟩
 | 7686 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 106),[(30424,1)]⟩
 | 7687 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 107),[(30425,1)]⟩
 | 7688 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 108),[(30427,1)]⟩
 | 7689 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0036.inputs 109),[(30426,4),(30427,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B18

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B18.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B18.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B18.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B18.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B18.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B18.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B18.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B18.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B18.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B18.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B18.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B18.count
