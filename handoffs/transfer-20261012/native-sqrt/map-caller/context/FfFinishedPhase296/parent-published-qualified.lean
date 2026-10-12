import Mathlib.Algebra.Field.Basic
import Mathlib.Data.List.Range
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FfFinishedPhase296
variable {F : Type} [Field F] [DecidableEq F]

structure Inner (F : Type) where
  k : Nat
  b2k : F
  z : F
  below : Bool

structure State (F : Type) where
  x : F
  b : F
  z : F
  v : Nat

def InnerDone (i : Inner F) : Prop :=
  i.k = 1 ∧ i.b2k = 1 ∧ i.z * i.z = 1 ∧ i.below = true

def Finished (input : F) (s : State F) : Prop :=
  s.x * s.x = input ∧ s.v = 1 ∧ s.b * s.b = 1 ∧ s.z * s.z = 1

def innerStep (v : Nat) (i : Inner F) (j : Nat) : Inner F :=
  let one := i.b2k = 1
  let squared := (if one then i.z else i.b2k) * (if one then i.z else i.b2k)
  let b2k := if one then i.b2k else squared
  let newZ := if one then squared else i.z
  let below := i.below && decide (j ≠ v)
  { k := if one then i.k else j
    b2k := b2k
    z := if below then newZ else i.z
    below := below }

theorem inner_done_step (i : Inner F) (done : InnerDone i) (j : Nat) (lower : 2 ≤ j) :
    InnerDone (innerStep 1 i j) := by
  have different : j ≠ 1 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) lower)
  have exactStep : innerStep 1 i j = ⟨1, 1, 1, true⟩ := by
    simp [innerStep, done.1, done.2.1, done.2.2.1, done.2.2.2, different]
  rw [exactStep]
  simp [InnerDone]

theorem inner_done_fold (indices : List Nat) (lower : ∀ j ∈ indices, 2 ≤ j)
    (i : Inner F) (done : InnerDone i) :
    InnerDone (indices.foldl (innerStep 1) i) := by
  induction indices generalizing i with
  | nil => exact done
  | cons j rest ih =>
    change InnerDone (rest.foldl (innerStep 1) (innerStep 1 i j))
    exact ih (fun index member => lower index (List.mem_cons_of_mem j member))
      (innerStep 1 i j) (inner_done_step i done j (lower j (List.mem_cons_self)))

theorem range_lower_bound (count : Nat) : ∀ j ∈ List.range' 2 count, 2 ≤ j := by
  intro j member
  obtain ⟨offset, _, equal⟩ := List.mem_range'.mp member
  rw [equal]
  exact Nat.le_add_right 2 _

def innerFor (maxV : Nat) (s : State F) : Inner F :=
  (List.range' 2 (maxV - 2)).foldl (innerStep s.v) ⟨1, s.b * s.b, s.z, true⟩

theorem inner_for_finished (input : F) (maxV : Nat) (s : State F)
    (finished : Finished input s) : InnerDone (innerFor maxV s) := by
  unfold innerFor
  rw [finished.2.1]
  exact inner_done_fold _ (range_lower_bound _) _
    ⟨rfl, finished.2.2.1, finished.2.2.2, rfl⟩

def outerStep (maxV : Nat) (s : State F) : State F :=
  let i := innerFor maxV s
  let newZ := i.z * i.z
  { x := if s.b = 1 then s.x else s.x * i.z
    b := s.b * newZ
    z := newZ
    v := i.k }

theorem outer_finished (input : F) (maxV : Nat) (s : State F)
    (finished : Finished input s) : Finished input (outerStep maxV s) := by
  have inner := inner_for_finished input maxV s finished
  refine ⟨?_, inner.1, ?_, ?_⟩
  · change (if s.b = 1 then s.x else s.x * (innerFor maxV s).z) *
      (if s.b = 1 then s.x else s.x * (innerFor maxV s).z) = input
    split_ifs
    · exact finished.1
    · rw [mul_mul_mul_comm, inner.2.2.1, mul_one]
      exact finished.1
  · change (s.b * ((innerFor maxV s).z * (innerFor maxV s).z)) *
      (s.b * ((innerFor maxV s).z * (innerFor maxV s).z)) = 1
    rw [inner.2.2.1, mul_one]
    exact finished.2.2.1
  · change ((innerFor maxV s).z * (innerFor maxV s).z) *
      ((innerFor maxV s).z * (innerFor maxV s).z) = 1
    rw [inner.2.2.1, one_mul]

def outerLoop (maxima : List Nat) (s : State F) : State F :=
  maxima.foldl (fun state maximum => outerStep maximum state) s

theorem finished_loop (input : F) (maxima : List Nat) (s : State F)
    (finished : Finished input s) : Finished input (outerLoop maxima s) := by
  induction maxima generalizing s with
  | nil => exact finished
  | cons maximum rest ih =>
    change Finished input (outerLoop rest (outerStep maximum s))
    exact ih (outerStep maximum s) (outer_finished input maximum s finished)

theorem finished_payload (input : F) (maxima : List Nat) (s : State F)
    (finished : Finished input s) :
    (outerLoop maxima s).x * (outerLoop maxima s).x = input :=
  (finished_loop input maxima s finished).1

end ShielddSecurity.FfFinishedPhase296

set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.Inner
#print axioms ShielddSecurity.FfFinishedPhase296.Inner
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.Inner.mk
#print axioms ShielddSecurity.FfFinishedPhase296.Inner.mk
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.Inner.k
#print axioms ShielddSecurity.FfFinishedPhase296.Inner.k
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.Inner.b2k
#print axioms ShielddSecurity.FfFinishedPhase296.Inner.b2k
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.Inner.z
#print axioms ShielddSecurity.FfFinishedPhase296.Inner.z
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.Inner.below
#print axioms ShielddSecurity.FfFinishedPhase296.Inner.below
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.State
#print axioms ShielddSecurity.FfFinishedPhase296.State
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.State.mk
#print axioms ShielddSecurity.FfFinishedPhase296.State.mk
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.State.x
#print axioms ShielddSecurity.FfFinishedPhase296.State.x
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.State.b
#print axioms ShielddSecurity.FfFinishedPhase296.State.b
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.State.z
#print axioms ShielddSecurity.FfFinishedPhase296.State.z
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.State.v
#print axioms ShielddSecurity.FfFinishedPhase296.State.v
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.InnerDone
#print axioms ShielddSecurity.FfFinishedPhase296.InnerDone
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.Finished
#print axioms ShielddSecurity.FfFinishedPhase296.Finished
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.innerStep
#print axioms ShielddSecurity.FfFinishedPhase296.innerStep
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.inner_done_step
#print axioms ShielddSecurity.FfFinishedPhase296.inner_done_step
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.inner_done_fold
#print axioms ShielddSecurity.FfFinishedPhase296.inner_done_fold
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.range_lower_bound
#print axioms ShielddSecurity.FfFinishedPhase296.range_lower_bound
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.innerFor
#print axioms ShielddSecurity.FfFinishedPhase296.innerFor
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.inner_for_finished
#print axioms ShielddSecurity.FfFinishedPhase296.inner_for_finished
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.outerStep
#print axioms ShielddSecurity.FfFinishedPhase296.outerStep
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.outer_finished
#print axioms ShielddSecurity.FfFinishedPhase296.outer_finished
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.outerLoop
#print axioms ShielddSecurity.FfFinishedPhase296.outerLoop
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.finished_loop
#print axioms ShielddSecurity.FfFinishedPhase296.finished_loop
set_option pp.all true in
#check @ShielddSecurity.FfFinishedPhase296.finished_payload
#print axioms ShielddSecurity.FfFinishedPhase296.finished_payload
