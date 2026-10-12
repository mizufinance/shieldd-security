import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0045
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B23
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 316).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9450 16
def localParent : Nat → Option Row
 | 9450 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 90),[(32188,1)]⟩
 | 9451 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 91),[(32189,1)]⟩
 | 9452 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 92),[(32191,1)]⟩
 | 9453 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 93),[(32190,4),(32191,1)]⟩
 | 9454 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 94),[(32192,1)]⟩
 | 9455 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 95),[(32193,1)]⟩
 | 9456 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 96),[(32195,1)]⟩
 | 9457 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 97),[(32194,4),(32195,1)]⟩
 | 9458 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 98),[(32196,1)]⟩
 | 9459 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 99),[(32197,1)]⟩
 | 9460 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 100),[(32199,1)]⟩
 | 9461 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 101),[(32198,4),(32199,1)]⟩
 | 9462 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 102),[(32200,1)]⟩
 | 9463 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 103),[(32201,1)]⟩
 | 9464 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 104),[(32203,1)]⟩
 | 9465 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 105),[(32202,4),(32203,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B23

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B23.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B23.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B23.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B23.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B23.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B23.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B23.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B23.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B23.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B23.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B23.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B23.count
