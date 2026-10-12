import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0016
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L01B07
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 60).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1272)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3682 16
def localParent : Nat → Option Row
 | 3682 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 236),[(26420,1)]⟩
 | 3683 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 237),[(26421,1)]⟩
 | 3684 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 238),[(26423,1)]⟩
 | 3685 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 239),[(26422,4),(26423,1)]⟩
 | 3686 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 240),[(26424,1)]⟩
 | 3687 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 241),[(26425,1)]⟩
 | 3688 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 242),[(26427,1)]⟩
 | 3689 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 243),[(26426,4),(26427,1)]⟩
 | 3690 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 244),[(26428,1)]⟩
 | 3691 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 245),[(26429,1)]⟩
 | 3692 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 246),[(26431,1)]⟩
 | 3693 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 247),[(26430,4),(26431,1)]⟩
 | 3694 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 248),[(26432,1)]⟩
 | 3695 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 249),[(26433,1)]⟩
 | 3696 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 250),[(26435,1)]⟩
 | 3697 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 251),[(26434,4),(26435,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L01B07

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B07.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B07.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B07.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B07.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B07.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B07.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B07.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B07.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B07.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B07.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B07.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B07.count
