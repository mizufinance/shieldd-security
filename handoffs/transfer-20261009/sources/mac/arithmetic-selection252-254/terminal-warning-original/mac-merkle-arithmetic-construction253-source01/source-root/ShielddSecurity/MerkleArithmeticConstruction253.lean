import ShielddSecurity.CapturedArithmeticSelection252
import ShielddSecurity.MerkleGlobalBody181
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleArithmeticConstruction253
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
theorem copy_rows (base : Nat → F) (i : Fin 15) (checked : MerkleGlobalBody181.copyCheck i=true) :
 Satisfies (CapturedFullRelation58.candidate base) (MerkleGlobalBody181.copyRows i) :=
 CapturedArithmeticSelection252.candidate_rows base
   (List.replicate (MerkleGlobalBody181.copyRows i).length 200769) (MerkleGlobalBody181.copyRows i)
   checked (CapturedArithmeticSelection252.copies_supported _)
theorem body_rows (base : Nat → F) (i : Fin 15) (checked : MerkleGlobalBody181.copyCheck i=true)
 (arithmetic : Satisfies (CapturedFullRelation58.candidate base) (MerkleGlobalBody181.arithmeticRows i)) :
 Satisfies (CapturedFullRelation58.candidate base) (MerkleFamily32Whole.rows (F:=F) i) := by
 rw [MerkleGlobalBody181.rows_exact]
 exact MerkleGlobalBody181.body_sound i _ arithmetic (copy_rows base i checked)
theorem candidate_zero (base : Nat → F) (one : base 0=1) : CapturedFullRelation58.candidate base 0=1 :=
 (CapturedFullRelation58.candidate_outside base 0 (by decide) (by decide)).trans one
end ShielddSecurity.MerkleArithmeticConstruction253

set_option pp.all true in
#check @ShielddSecurity.MerkleArithmeticConstruction253.copy_rows
#print axioms ShielddSecurity.MerkleArithmeticConstruction253.copy_rows
set_option pp.all true in
#check @ShielddSecurity.MerkleArithmeticConstruction253.body_rows
#print axioms ShielddSecurity.MerkleArithmeticConstruction253.body_rows
set_option pp.all true in
#check @ShielddSecurity.MerkleArithmeticConstruction253.candidate_zero
#print axioms ShielddSecurity.MerkleArithmeticConstruction253.candidate_zero
