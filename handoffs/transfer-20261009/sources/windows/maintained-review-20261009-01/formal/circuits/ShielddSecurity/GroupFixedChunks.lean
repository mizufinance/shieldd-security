import ShielddSecurity.GroupFixedWindows

set_option maxHeartbeats 300000

namespace ShielddSecurity.GroupFixedChunks

open GroupFixedWindows

variable {F : Type} [Field F]

/-- The carried native base is computed by the captured local table steps. -/
def fixedTraceBase : Group.Point F → List (FixedWindowWitness F) → Group.Point F
  | base, [] => base
  | _, window :: tail => fixedTraceBase window.nextBase tail

theorem trace_append (d : F) (front back : List (FixedWindowWitness F))
    (input base : Group.Point F)
    (first : FixedTraceEquations d input base front)
    (second : FixedTraceEquations d (fixedTraceOutput input front)
      (fixedTraceBase base front) back) :
    FixedTraceEquations d input base (front ++ back) := by
  induction front generalizing input base with
  | nil => exact second
  | cons window tail ih =>
    exact ⟨first.1, ih window.output window.nextBase first.2 second⟩

def ChunkEquations (d : F) : Group.Point F → Group.Point F →
    List (List (FixedWindowWitness F)) → Prop
  | _, _, [] => True
  | input, base, front :: tail => FixedTraceEquations d input base front ∧
      ChunkEquations d (fixedTraceOutput input front) (fixedTraceBase base front) tail

/-- Composition is symbolic in the number and sizes of chunks. -/
theorem chunks_trace (d : F) (chunks : List (List (FixedWindowWitness F)))
    (input base : Group.Point F) (checked : ChunkEquations d input base chunks) :
    FixedTraceEquations d input base chunks.flatten := by
  induction chunks generalizing input base with
  | nil => exact True.intro
  | cons front tail ih =>
    exact trace_append d front tail.flatten input base checked.1
      (ih _ _ checked.2)

def windowBits (windows : List (FixedWindowWitness F)) : List Bool :=
  windows.flatMap (fun window => [window.low,window.high])

/-- Ascending radix-four windows pair exactly their low and high Boolean bits. -/
theorem window_bits_digits (windows : List (FixedWindowWitness F)) :
    TransferWindows.pairDigits (windowBits windows) = windows.map fixedDigit := by
  induction windows with
  | nil => rfl
  | cons window tail ih =>
    change ((if window.low then 1 else 0) + 2 * (if window.high then 1 else 0)) ::
      TransferWindows.pairDigits (windowBits tail) = fixedDigit window :: tail.map fixedDigit
    rw [ih]
    congr 1
    cases lowValue : window.low <;> cases highValue : window.high <;>
      simp [fixedDigit,lowValue,highValue]

set_option pp.all true in
#check @trace_append
#print axioms trace_append
set_option pp.all true in
#check @chunks_trace
#print axioms chunks_trace
set_option pp.all true in
#check @window_bits_digits
#print axioms window_bits_digits

end ShielddSecurity.GroupFixedChunks
