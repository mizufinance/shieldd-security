import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0023
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B10
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 108).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5002 16
def localParent : Nat → Option Row
 | 5002 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 138),[(27740,1)]⟩
 | 5003 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 139),[(27741,1)]⟩
 | 5004 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 140),[(27743,1)]⟩
 | 5005 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 141),[(27742,4),(27743,1)]⟩
 | 5006 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 142),[(27744,1)]⟩
 | 5007 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 143),[(27745,1)]⟩
 | 5008 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 144),[(27747,1)]⟩
 | 5009 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 145),[(27746,4),(27747,1)]⟩
 | 5010 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 146),[(27748,1)]⟩
 | 5011 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 147),[(27749,1)]⟩
 | 5012 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 148),[(27751,1)]⟩
 | 5013 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 149),[(27750,4),(27751,1)]⟩
 | 5014 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 150),[(27752,1)]⟩
 | 5015 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 151),[(27753,1)]⟩
 | 5016 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 152),[(27755,1)]⟩
 | 5017 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 153),[(27754,4),(27755,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B10

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B10.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B10.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B10.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B10.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B10.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B10.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B10.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B10.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B10.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B10.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B10.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B10.count
