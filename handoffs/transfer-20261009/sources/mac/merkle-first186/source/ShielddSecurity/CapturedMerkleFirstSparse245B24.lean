import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0014
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleFirstSparse245B24
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 344).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 424)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3118 16
def localParent : Nat → Option Row
 | 3118 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 88),[(25856,1)]⟩
 | 3119 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 89),[(25857,1)]⟩
 | 3120 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 90),[(25859,1)]⟩
 | 3121 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 91),[(25858,4),(25859,1)]⟩
 | 3122 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 92),[(25860,1)]⟩
 | 3123 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 93),[(25861,1)]⟩
 | 3124 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 94),[(25863,1)]⟩
 | 3125 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 95),[(25862,4),(25863,1)]⟩
 | 3126 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 96),[(25864,1)]⟩
 | 3127 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 97),[(25865,1)]⟩
 | 3128 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 98),[(25867,1)]⟩
 | 3129 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 99),[(25866,4),(25867,1)]⟩
 | 3130 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 100),[(25868,1)]⟩
 | 3131 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 101),[(25869,1)]⟩
 | 3132 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 102),[(25871,1)]⟩
 | 3133 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 103),[(25870,4),(25871,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleFirstSparse245B24

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B24.rows
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B24.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B24.indices
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B24.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B24.localParent
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B24.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B24.localCheck
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B24.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B24.local_checked
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B24.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B24.count
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B24.count
