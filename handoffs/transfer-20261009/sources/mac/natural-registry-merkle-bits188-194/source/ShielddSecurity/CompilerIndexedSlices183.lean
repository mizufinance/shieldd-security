import ShielddSecurity.CompilerSelectedChunks172
import ShielddSecurity.CompilerSegmentChain33
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CompilerIndexedSlices183
open Compiler CompilerSelectedChunks172
def slicesAt (rows : List Row) (offset : Nat) : List Nat → List (List Row)
 | [] => []
 | width::widths => (rows.drop offset).take width :: slicesAt rows (offset+width) widths
theorem slicesAt_eq (rows : List Row) (offset : Nat) (widths : List Nat) :
 slicesAt rows offset widths=slices (rows.drop offset) widths := by
 induction widths generalizing offset with
 | nil => rfl
 | cons width widths ih => rw [slicesAt,slices,ih,List.drop_drop]
theorem partition (rows : List Row) (widths : List Nat) (enough : rows.length≤widths.sum) :
 (slicesAt rows 0 widths).flatten=rows := by
 rw [slicesAt_eq,List.drop_zero,slices_flatten,List.take_of_length_le enough]
variable {F : Type} [Field F]
theorem sound (rows : List Row) (widths : List Nat) (enough : rows.length≤widths.sum)
 (rho : Nat → F) (sat : AllSatisfied rho (slicesAt rows 0 widths)) : Satisfies rho rows := by
 rw [←partition rows widths enough]
 exact flatten_sound rho _ sat
theorem chain_sound (copy : Nat) (piece : Nat → CompilerSegmentCompletion11.Segment F copy)
 (count : Nat) (rho : Nat → F) (sat : ∀ i<count,Satisfies rho (piece i).rows) :
 Satisfies rho (CompilerSegmentChain33.rows copy piece count) := by
 induction count with
 | zero => intro row member;cases member
 | succ count ih =>
   intro row member
   rcases List.mem_append.mp member with member|member
   · exact ih (fun i less => sat i (by omega)) row member
   · exact sat count (by omega) row member
end ShielddSecurity.CompilerIndexedSlices183

set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedSlices183.slicesAt
#print axioms ShielddSecurity.CompilerIndexedSlices183.slicesAt
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedSlices183.slicesAt_eq
#print axioms ShielddSecurity.CompilerIndexedSlices183.slicesAt_eq
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedSlices183.partition
#print axioms ShielddSecurity.CompilerIndexedSlices183.partition
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedSlices183.sound
#print axioms ShielddSecurity.CompilerIndexedSlices183.sound
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedSlices183.chain_sound
#print axioms ShielddSecurity.CompilerIndexedSlices183.chain_sound
