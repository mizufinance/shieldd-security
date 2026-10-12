import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0022
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B26
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 364).take 8).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4834 8
def localParent : Nat → Option Row
 | 4834 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 140),[(27572,1)]⟩
 | 4835 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 141),[(27573,1)]⟩
 | 4836 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 142),[(27575,1)]⟩
 | 4837 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 143),[(27574,4),(27575,1)]⟩
 | 4838 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 144),[(27576,1)]⟩
 | 4839 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 145),[(27577,1)]⟩
 | 4840 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 146),[(27579,1)]⟩
 | 4841 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 147),[(27578,4),(27579,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=8 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B26

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B26.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B26.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B26.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B26.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B26.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B26.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B26.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B26.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B26.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B26.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B26.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B26.count
