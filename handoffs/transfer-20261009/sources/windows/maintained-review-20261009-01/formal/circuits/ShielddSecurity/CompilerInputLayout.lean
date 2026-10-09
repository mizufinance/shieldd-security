import ShielddSecurity.Compiler

set_option maxHeartbeats 50000

namespace ShielddSecurity.CompilerInputLayout

/-- Allocation counters for successful, nonoverflowing circuit construction.
The source interpretation is separate: the exact Transfer suffix allocates its
claimed statement witness, then uses only constants, arithmetic nodes and an
assertion. The hash suffix has no division or witness allocation. -/
structure Counters where
  witnesses : Nat
  constants : Nat
  nodes : Nat
  assertions : Nat

inductive TailOperation where
  | constant
  | node
  | assertion

def append (state : Counters) : TailOperation → Counters
  | .constant => { state with constants := state.constants + 1 }
  | .node => { state with nodes := state.nodes + 1 }
  | .assertion => { state with assertions := state.assertions + 1 }

def tail (state : Counters) : List TailOperation → Counters
  | [] => state
  | operation :: rest => tail (append state operation) rest

/-- The exact `next_witness` counter update; the returned index is the old
counter. The following hash/assertion operations do not allocate witnesses. -/
def finish (state : Counters) (operations : List TailOperation) : Counters × Nat :=
  (tail { state with witnesses := state.witnesses + 1 } operations, state.witnesses)

/-- `Compiler::new`: one constant column, selected public columns, committed
columns, then all source witnesses, before any materialized product column. -/
def productOrigin (publicCount committedCount witnesses : Nat) : Nat :=
  1 + publicCount + committedCount + witnesses

theorem tail_witness_count (state : Counters) (operations : List TailOperation) :
    (tail state operations).witnesses = state.witnesses := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      rw [tail, ih]
      cases operation <;> rfl

theorem finished_witness_count (state : Counters) (operations : List TailOperation) :
    (finish state operations).1.witnesses = (finish state operations).2 + 1 := by
  exact tail_witness_count { state with witnesses := state.witnesses + 1 } operations

theorem finished_product_origin (state : Counters) (operations : List TailOperation)
    (publicCount committedCount : Nat) :
    productOrigin publicCount committedCount (finish state operations).1.witnesses =
      1 + publicCount + committedCount + ((finish state operations).2 + 1) := by
  rw [productOrigin, finished_witness_count]

theorem transfer_product_origin (state : Counters) (operations : List TailOperation)
    (observedPublic : (finish state operations).2 = 22734) :
    productOrigin 1 1 (finish state operations).1.witnesses = 22738 := by
  rw [finished_product_origin, observedPublic]

set_option pp.all true in
#check @tail_witness_count
#print axioms tail_witness_count
set_option pp.all true in
#check @finished_witness_count
#print axioms finished_witness_count
set_option pp.all true in
#check @finished_product_origin
#print axioms finished_product_origin
set_option pp.all true in
#check @transfer_product_origin
#print axioms transfer_product_origin

end ShielddSecurity.CompilerInputLayout
