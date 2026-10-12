import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0014
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L00B07
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 60).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 848)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3258 16
def localParent : Nat → Option Row
 | 3258 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 228),[(25996,1)]⟩
 | 3259 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 229),[(25997,1)]⟩
 | 3260 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 230),[(25999,1)]⟩
 | 3261 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 231),[(25998,4),(25999,1)]⟩
 | 3262 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 232),[(26000,1)]⟩
 | 3263 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 233),[(26001,1)]⟩
 | 3264 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 234),[(26003,1)]⟩
 | 3265 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 235),[(26002,4),(26003,1)]⟩
 | 3266 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 236),[(26004,1)]⟩
 | 3267 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 237),[(26005,1)]⟩
 | 3268 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 238),[(26007,1)]⟩
 | 3269 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 239),[(26006,4),(26007,1)]⟩
 | 3270 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 240),[(26008,1)]⟩
 | 3271 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 241),[(26009,1)]⟩
 | 3272 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 242),[(26011,1)]⟩
 | 3273 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 243),[(26010,4),(26011,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L00B07

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B07.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B07.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B07.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B07.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B07.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B07.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B07.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B07.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B07.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B07.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B07.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B07.count
