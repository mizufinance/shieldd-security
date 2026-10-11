import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.CompilerSelectedChunks172
open Compiler CompilerAssertionBlock51
-- Symbolic list composition; no expansion of literal LC terms.
def slices (rows : List Row) : List Nat → List (List Row)
  | [] => []
  | width::widths => rows.take width :: slices (rows.drop width) widths
theorem slices_flatten (rows : List Row) (widths : List Nat) :
    (slices rows widths).flatten=rows.take widths.sum := by
  induction widths generalizing rows with
  | nil => rfl
  | cons width widths ih =>
    rw [slices,List.flatten_cons,ih,←List.take_add]
    rfl
variable {F : Type} [Field F]
def AllSatisfied (rho : Nat → F) : List (List Row) → Prop
  | [] => True
  | rows::rest => Satisfies rho rows ∧ AllSatisfied rho rest
theorem flatten_sound (rho : Nat → F) (chunks : List (List Row))
    (satisfied : AllSatisfied rho chunks) : Satisfies rho chunks.flatten := by
  revert satisfied
  induction chunks with
  | nil => intro satisfied row member;cases member
  | cons rows chunks ih =>
    intro satisfied row member
    rcases List.mem_append.mp member with member|member
    · exact satisfied.1 row member
    · exact ih satisfied.2 row member
end ShielddSecurity.CompilerSelectedChunks172

set_option pp.all true in
#check @ShielddSecurity.CompilerSelectedChunks172.slices
#print axioms ShielddSecurity.CompilerSelectedChunks172.slices
set_option pp.all true in
#check @ShielddSecurity.CompilerSelectedChunks172.slices_flatten
#print axioms ShielddSecurity.CompilerSelectedChunks172.slices_flatten
set_option pp.all true in
#check @ShielddSecurity.CompilerSelectedChunks172.AllSatisfied
#print axioms ShielddSecurity.CompilerSelectedChunks172.AllSatisfied
set_option pp.all true in
#check @ShielddSecurity.CompilerSelectedChunks172.flatten_sound
#print axioms ShielddSecurity.CompilerSelectedChunks172.flatten_sound
