import ShielddSecurity.Poseidon

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

namespace ShielddSecurity.PoseidonRoundComposition

variable {F : Type} [Field F]

/-- A standalone prefix round only stores its own ARK row. The full table join
must compare that exact index and the complete MDS matrix, rather than require
the prefix's constant ARK function to equal the whole permutation's table. -/
theorem round_agrees {width : Nat} (parameters other : Poseidon.Parameters F width)
    (index : Nat) (state : Poseidon.State F width)
    (ark : parameters.ark index = other.ark index) (mds : parameters.mds = other.mds) :
    Poseidon.round parameters index state = Poseidon.round other index state := by
  unfold Poseidon.round
  rw [ark,mds]

theorem cast_round_agrees {width : Nat} (parameters other : Poseidon.Parameters Int width)
    (index : Nat) (state : Poseidon.State F width)
    (ark : parameters.ark index = other.ark index) (mds : parameters.mds = other.mds) :
    Poseidon.round (Poseidon.castParameters parameters) index state =
      Poseidon.round (Poseidon.castParameters other) index state := by
  apply round_agrees
  · funext column
    exact congrArg (fun coefficient : Int => (coefficient : F)) (congrFun ark column)
  · funext row column
    exact congrArg (fun coefficient : Int => (coefficient : F)) (congrFun (congrFun mds row) column)

set_option pp.all true in
#check @round_agrees
#print axioms round_agrees
set_option pp.all true in
#check @cast_round_agrees
#print axioms cast_round_agrees

end ShielddSecurity.PoseidonRoundComposition
