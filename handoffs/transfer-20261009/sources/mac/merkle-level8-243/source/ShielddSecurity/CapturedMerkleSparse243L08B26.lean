import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0033
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B26
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 364).take 8).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6954 8
def localParent : Nat → Option Row
 | 6954 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 90),[(29692,1)]⟩
 | 6955 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 91),[(29693,1)]⟩
 | 6956 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 92),[(29695,1)]⟩
 | 6957 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 93),[(29694,4),(29695,1)]⟩
 | 6958 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 94),[(29696,1)]⟩
 | 6959 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 95),[(29697,1)]⟩
 | 6960 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 96),[(29699,1)]⟩
 | 6961 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 97),[(29698,4),(29699,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=8 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B26

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B26.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B26.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B26.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B26.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B26.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B26.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B26.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B26.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B26.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B26.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B26.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B26.count
