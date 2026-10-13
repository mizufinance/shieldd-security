import ShielddSecurity.SharedWordWitness221
import ShielddSecurity.CapturedFourSubgroupSeed89
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedZeroConstant336
open CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem word (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) (one : base 0=1) :
    SharedWordWitness221.completed base numbers fallback 0=1 :=
  (CapturedFullRelation58.candidate_outside (SharedWordWitness221.seeded base numbers fallback) 0
    (Or.inl (by decide)) (by constructor <;> decide)).trans
    ((SharedWordWitness221.seeded_fixed base numbers fallback).1.trans one)
theorem subgroup (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (numbers : Nat → Nat) (fallback : Nat → Bool) (one : base 0=1) :
    SharedWordWitness221.completed (CapturedFourSubgroupSeed89.seeded base initial) numbers fallback 0=1 :=
  word (CapturedFourSubgroupSeed89.seeded base initial) numbers fallback
    ((CapturedFourSubgroupSeed89.seeded_outside base initial 0 (by decide)).trans one)
end ShielddSecurity.SharedZeroConstant336
set_option pp.all true in
#check @ShielddSecurity.SharedZeroConstant336.word
#print axioms ShielddSecurity.SharedZeroConstant336.word
set_option pp.all true in
#check @ShielddSecurity.SharedZeroConstant336.subgroup
#print axioms ShielddSecurity.SharedZeroConstant336.subgroup
