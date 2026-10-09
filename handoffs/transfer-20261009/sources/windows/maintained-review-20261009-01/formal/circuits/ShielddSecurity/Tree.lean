import ShielddSecurity.Range

set_option maxHeartbeats 200000

namespace ShielddSecurity.Tree

variable {F : Type} [Field F]

/-- Independent ordered quaternary-path semantics: siblings retain their order
while the current node occupies the selected position. -/
def children (low high : Bool) (node first second third : F) : List F :=
  match high, low with
  | false, false => [node, first, second, third]
  | false, true => [first, node, second, third]
  | true, false => [first, second, node, third]
  | true, true => [first, second, third, node]

def select (bit yes no : F) : F := bit * yes + (1 - bit) * no

/-- Polynomial wiring used by the runtime's four-child Merkle gadget. Hashing
these values, level/domain binding and compiled-row membership are separate
obligations. This definition does not pretend to prove those joins. -/
def wiredChildren (low high node first second third : F) : List F :=
  let leftSwap := low * (first - node)
  let rightSwap := low * (third - node)
  [select high first (node + leftSwap),
   select high second (first - leftSwap),
   select high (node + rightSwap) second,
   select high (third - rightSwap) third]

def bit (value : Bool) : F := if value then 1 else 0

/-- The four polynomial cases agree with the independent child-position
specification, including the sibling order in both halves. -/
theorem wiring_correct (low high : Bool) (node first second third : F) :
    wiredChildren (bit low) (bit high) node first second third =
      children low high node first second third := by
  cases low <;> cases high <;> simp [wiredChildren, select, bit, children]

/-- Soundness covers arbitrary field assignments satisfying bit constraints,
not just bit values returned by the honest witness constructor. -/
theorem wiring_sound (low high node first second third : F)
    (lowBoolean : Square low low) (highBoolean : Square high high) :
    ∃ lowBit highBit : Bool, bit lowBit = low ∧ bit highBit = high ∧
      wiredChildren low high node first second third =
        children lowBit highBit node first second third := by
  rcases boolean_sound low lowBoolean with lo | lo <;>
    rcases boolean_sound high highBoolean with hi | hi
  · exact ⟨false, false, by simp [bit, lo], by simp [bit, hi],
      by simpa [bit, lo, hi] using wiring_correct false false node first second third⟩
  · exact ⟨false, true, by simp [bit, lo], by simp [bit, hi],
      by simpa [bit, lo, hi] using wiring_correct false true node first second third⟩
  · exact ⟨true, false, by simp [bit, lo], by simp [bit, hi],
      by simpa [bit, lo, hi] using wiring_correct true false node first second third⟩
  · exact ⟨true, true, by simp [bit, lo], by simp [bit, hi],
      by simpa [bit, lo, hi] using wiring_correct true true node first second third⟩

/-- Every child position supplies a legal assignment to these local gates.
This is not completeness of an entire Merkle path or compiled relation. -/
theorem wiring_complete (low high : Bool) (node first second third : F) :
    Square (bit low : F) (bit low) ∧ Square (bit high : F) (bit high) ∧
      wiredChildren (bit low) (bit high) node first second third =
        children low high node first second third := by
  refine ⟨?_, ?_, wiring_correct low high node first second third⟩
  · cases low <;> simp [Square, bit]
  · cases high <;> simp [Square, bit]

set_option pp.all true in
#check @wiring_correct
#print axioms wiring_correct
set_option pp.all true in
#check @wiring_sound
#print axioms wiring_sound
set_option pp.all true in
#check @wiring_complete
#print axioms wiring_complete

end ShielddSecurity.Tree
