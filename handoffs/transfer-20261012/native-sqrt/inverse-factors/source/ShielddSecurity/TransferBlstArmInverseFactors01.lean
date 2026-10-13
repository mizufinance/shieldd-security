import ShielddSecurity.TransferBlstArmSqrtWhile01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseFactors01

/-! Signed integer interpretation of the locked exact inner_loop_62 factor
updates: parity-controlled subtraction, borrow-controlled exchange, shift,
and doubled second row. Symbolic matrix tracking is proved for arbitrary
counts. It does not infer the preceding approximate 31-bit batch states,
factor register bounds, gcd termination, 512-bit correction or native ISA. -/

structure SourceFactors where
  a : Nat
  b : Nat
  f0 : Int
  g0 : Int
  f1 : Int
  g1 : Int

def sourceFactorInitial (a b : Nat) : SourceFactors := ⟨a,b,1,0,0,1⟩

def sourceFactorStep (s : SourceFactors) : SourceFactors :=
  if s.a%2=0 then ⟨s.a/2,s.b,s.f0,s.g0,2*s.f1,2*s.g1⟩
  else if s.b≤s.a then ⟨(s.a-s.b)/2,s.b,s.f0-s.f1,s.g0-s.g1,2*s.f1,2*s.g1⟩
  else ⟨(s.b-s.a)/2,s.a,s.f1-s.f0,s.g1-s.g0,2*s.f0,2*s.g0⟩

def Tracks (a b : Nat) (scale : Int) (s : SourceFactors) : Prop :=
  scale*(s.a:Int)=s.f0*(a:Int)+s.g0*(b:Int) ∧ scale*(s.b:Int)=s.f1*(a:Int)+s.g1*(b:Int)

theorem original_factor_step_retains_odd_second_input (s : SourceFactors) (odd : s.b%2=1) :
    (sourceFactorStep s).b%2=1 := by
  rw [sourceFactorStep]
  split
  · exact odd
  · split
    · exact odd
    · change s.a%2=1
      have modBound := Nat.mod_lt s.a (by decide : 0<2)
      omega

theorem original_factor_step_derives_the_exact_doubled_input_rows
    (a b : Nat) (scale : Int) (s : SourceFactors) (odd : s.b%2=1) (tracked : Tracks a b scale s) :
    Tracks a b (2*scale) (sourceFactorStep s) := by
  by_cases even : s.a%2=0
  · have halfNat : 2*(s.a/2)=s.a := by omega
    have half : (s.a:Int)=2*((s.a/2:Nat):Int) := by exact_mod_cast halfNat.symm
    rw [sourceFactorStep,if_pos even]
    change (2*scale)*((s.a/2:Nat):Int)=s.f0*(a:Int)+s.g0*(b:Int) ∧
      (2*scale)*(s.b:Int)=(2*s.f1)*(a:Int)+(2*s.g1)*(b:Int)
    constructor
    · calc
        _ = scale*(s.a:Int) := by rw [half]; ring
        _ = _ := tracked.1
    · calc
        _ = 2*(scale*(s.b:Int)) := by ring
        _ = 2*(s.f1*(a:Int)+s.g1*(b:Int)) := by rw [tracked.2]
        _ = _ := by ring
  · have aOdd : s.a%2=1 := by have bound := Nat.mod_lt s.a (by decide : 0<2); omega
    by_cases ordered : s.b≤s.a
    · have halfNat : 2*((s.a-s.b)/2)=s.a-s.b := by omega
      have half : (s.a:Int)-(s.b:Int)=2*(((s.a-s.b)/2:Nat):Int) := by
        have casted := congrArg (fun value : Nat => (value:Int)) halfNat
        simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub ordered] using casted.symm
      rw [sourceFactorStep,if_neg even,if_pos ordered]
      change (2*scale)*(((s.a-s.b)/2:Nat):Int)=(s.f0-s.f1)*(a:Int)+(s.g0-s.g1)*(b:Int) ∧
        (2*scale)*(s.b:Int)=(2*s.f1)*(a:Int)+(2*s.g1)*(b:Int)
      constructor
      · calc
          _ = scale*((s.a:Int)-(s.b:Int)) := by rw [half]; ring
          _ = _ := by rw [mul_sub,tracked.1,tracked.2]; ring
      · calc
          _ = 2*(scale*(s.b:Int)) := by ring
          _ = 2*(s.f1*(a:Int)+s.g1*(b:Int)) := by rw [tracked.2]
          _ = _ := by ring
    · have reversed : s.a≤s.b := by omega
      have halfNat : 2*((s.b-s.a)/2)=s.b-s.a := by omega
      have half : (s.b:Int)-(s.a:Int)=2*(((s.b-s.a)/2:Nat):Int) := by
        have casted := congrArg (fun value : Nat => (value:Int)) halfNat
        simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub reversed] using casted.symm
      rw [sourceFactorStep,if_neg even,if_neg ordered]
      change (2*scale)*(((s.b-s.a)/2:Nat):Int)=(s.f1-s.f0)*(a:Int)+(s.g1-s.g0)*(b:Int) ∧
        (2*scale)*(s.a:Int)=(2*s.f0)*(a:Int)+(2*s.g0)*(b:Int)
      constructor
      · calc
          _ = scale*((s.b:Int)-(s.a:Int)) := by rw [half]; ring
          _ = _ := by rw [mul_sub,tracked.2,tracked.1]; ring
      · calc
          _ = 2*(scale*(s.a:Int)) := by ring
          _ = 2*(s.f0*(a:Int)+s.g0*(b:Int)) := by rw [tracked.1]
          _ = _ := by ring

def sourceFactorWalk : Nat → SourceFactors → SourceFactors
  | 0,s => s
  | count+1,s => sourceFactorWalk count (sourceFactorStep s)

theorem symbolic_original_factor_walk_derives_all_scaled_input_rows
    (count a b : Nat) (scale : Int) (s : SourceFactors) (odd : s.b%2=1) (tracked : Tracks a b scale s) :
    (sourceFactorWalk count s).b%2=1 ∧ Tracks a b ((2:Int)^count*scale) (sourceFactorWalk count s) := by
  induction count generalizing s scale with
  | zero => exact ⟨odd,by simpa only [pow_zero,one_mul,sourceFactorWalk] using tracked⟩
  | succ count ih =>
      have next := ih (2*scale) (sourceFactorStep s) (original_factor_step_retains_odd_second_input s odd)
        (original_factor_step_derives_the_exact_doubled_input_rows a b scale s odd tracked)
      have scaled : (2:Int)^count*(2*scale)=(2:Int)^(count+1)*scale := by rw [pow_succ]; ring
      rw [scaled] at next
      exact next

theorem original_initialized_factor_walk_derives_exact_scaled_input_rows
    (count a b : Nat) (odd : b%2=1) :
    Tracks a b ((2:Int)^count) (sourceFactorWalk count (sourceFactorInitial a b)) := by
  have initial : Tracks a b 1 (sourceFactorInitial a b) := by simp only [Tracks,sourceFactorInitial,one_mul,zero_mul,add_zero,zero_add,and_self]
  have all := symbolic_original_factor_walk_derives_all_scaled_input_rows count a b 1 (sourceFactorInitial a b) odd initial
  simpa only [mul_one] using all.2

set_option pp.all true in
#check @sourceFactorInitial
#print axioms sourceFactorInitial
set_option pp.all true in
#check @sourceFactorStep
#print axioms sourceFactorStep
set_option pp.all true in
#check @Tracks
#print axioms Tracks
set_option pp.all true in
#check @original_factor_step_retains_odd_second_input
#print axioms original_factor_step_retains_odd_second_input
set_option pp.all true in
#check @original_factor_step_derives_the_exact_doubled_input_rows
#print axioms original_factor_step_derives_the_exact_doubled_input_rows
set_option pp.all true in
#check @sourceFactorWalk
#print axioms sourceFactorWalk
set_option pp.all true in
#check @symbolic_original_factor_walk_derives_all_scaled_input_rows
#print axioms symbolic_original_factor_walk_derives_all_scaled_input_rows
set_option pp.all true in
#check @original_initialized_factor_walk_derives_exact_scaled_input_rows
#print axioms original_initialized_factor_walk_derives_exact_scaled_input_rows
end ShielddSecurity.TransferBlstArmInverseFactors01
