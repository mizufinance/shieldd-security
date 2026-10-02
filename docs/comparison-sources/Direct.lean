import SpendComparison.Contract
import Clean.Utils.FiniteField

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace SpendComparison.Direct
variable {F : Type} [FiniteField F]

/-- Fair comparison restricts the direct arm to the identical field interface. -/
theorem sound (v : Values F) (holds : Gates v) : Meaning v := gates_sound v holds

theorem complete (v : Values F) (legal : Meaning v) : Gates v := gates_complete v legal

/-- Constructive completion is identity: no gate-local witness is needed. -/
def completeInput (v : Values F) : Values F := v

theorem completion_preserves (v : Values F) : completeInput v = v := rfl

theorem completed_gates (v : Values F) (legal : Meaning v) :
    Gates (completeInput v) := gates_complete v legal

#print axioms sound
#print axioms complete
#print axioms completion_preserves
#print axioms completed_gates
end SpendComparison.Direct
