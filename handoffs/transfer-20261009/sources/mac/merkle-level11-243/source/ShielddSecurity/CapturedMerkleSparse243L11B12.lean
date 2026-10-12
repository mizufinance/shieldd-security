import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0038
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L11B12
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 140).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5512)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8002 16
def localParent : Nat → Option Row
 | 8002 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 16),[(30740,1)]⟩
 | 8003 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 17),[(30741,1)]⟩
 | 8004 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 18),[(30743,1)]⟩
 | 8005 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 19),[(30742,4),(30743,1)]⟩
 | 8006 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 20),[(30744,1)]⟩
 | 8007 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 21),[(30745,1)]⟩
 | 8008 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 22),[(30747,1)]⟩
 | 8009 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 23),[(30746,4),(30747,1)]⟩
 | 8010 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 24),[(30748,1)]⟩
 | 8011 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 25),[(30749,1)]⟩
 | 8012 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 26),[(30751,1)]⟩
 | 8013 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 27),[(30750,4),(30751,1)]⟩
 | 8014 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 28),[(30752,1)]⟩
 | 8015 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 29),[(30753,1)]⟩
 | 8016 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 30),[(30755,1)]⟩
 | 8017 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0038.inputs 31),[(30754,4),(30755,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L11B12

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B12.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B12.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B12.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B12.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B12.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B12.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B12.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B12.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B12.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B12.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B12.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B12.count
