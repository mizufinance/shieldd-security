import ShielddSecurity.Range
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.BinaryComparison100
variable {F : Type} [Field F]
def bit (value : Bool) : F := if value then 1 else 0
def step (flag a b : F) : F :=
  let x:=1-a
  let both:=x*b
  both+flag*(x+b-(both+both))
def scan (flag : F) : List (Bool × Bool) → F
  | [] => flag
  | (a,b)::tail => scan (step flag (bit a) (bit b)) tail

theorem step_sound (a b : Bool) (left right scale : Nat) (leftBound : left<scale) (rightBound : right<scale) :
    step (if left≤right then (1:F) else 0) (bit a) (bit b)=
      if left+scale*(if a then 1 else 0)≤right+scale*(if b then 1 else 0) then 1 else 0 := by
  cases a <;> cases b
  · simp only [Bool.false_eq_true,if_false,step,bit,sub_zero,mul_zero,add_zero,zero_add,mul_one]
  · have bound : left≤right+scale := by omega
    simp only [Bool.false_eq_true,Bool.true_eq_true,if_false,if_true,step,bit,sub_zero,mul_one,mul_zero,add_zero]
    rw [if_pos bound]
    ring
  · have bound : ¬left+scale≤right := by omega
    simp only [Bool.false_eq_true,Bool.true_eq_true,if_false,if_true,step,bit,sub_self,zero_mul,mul_zero,add_zero,zero_add]
    rw [if_neg bound]
  · simp only [Bool.true_eq_true,if_true,step,bit,sub_self,zero_mul,mul_zero,add_zero,zero_add,mul_one]
    have same : left+scale≤right+scale ↔ left≤right := by omega
    rw [same]

theorem scan_sound (pairs : List (Bool × Bool)) (left right scale : Nat)
    (leftBound : left<scale) (rightBound : right<scale) :
    scan (if left≤right then (1:F) else 0) pairs=
      if left+scale*binary (pairs.map Prod.fst)≤right+scale*binary (pairs.map Prod.snd) then 1 else 0 := by
  induction pairs generalizing left right scale with
  | nil => simp only [scan,List.map_nil,binary,mul_zero,add_zero]
  | cons pair pairs ih =>
    rcases pair with ⟨a,b⟩
    rw [scan,step_sound a b left right scale leftBound rightBound]
    have lb : left+scale*(if a then 1 else 0)<scale*2 := by cases a <;> simp only [Bool.false_eq_true,Bool.true_eq_true,if_false,if_true,mul_zero,mul_one,add_zero] <;> omega
    have rb : right+scale*(if b then 1 else 0)<scale*2 := by cases b <;> simp only [Bool.false_eq_true,Bool.true_eq_true,if_false,if_true,mul_zero,mul_one,add_zero] <;> omega
    have h:=ih (left+scale*(if a then 1 else 0)) (right+scale*(if b then 1 else 0)) (scale*2) lb rb
    simpa only [List.map_cons,Prod.fst,Prod.snd,binary,Nat.mul_add,Nat.mul_assoc,Nat.add_assoc] using h

def compare (pairs : List (Bool × Bool)) : F := scan 1 pairs

theorem compare_exact (pairs : List (Bool × Bool)) :
    compare (F:=F) pairs=if binary (pairs.map Prod.fst)≤binary (pairs.map Prod.snd) then 1 else 0 := by
  have h:=scan_sound (F:=F) pairs 0 0 1 (by decide) (by decide)
  simpa only [compare,Nat.zero_le,if_true,Nat.one_mul,Nat.zero_add] using h

theorem compare_complete (pairs : List (Bool × Bool))
    (bound : binary (pairs.map Prod.fst)≤binary (pairs.map Prod.snd)) : compare (F:=F) pairs=1 := by
  rw [compare_exact,if_pos bound]

theorem compare_boolean (pairs : List (Bool × Bool)) : Square (compare (F:=F) pairs) (compare (F:=F) pairs) := by
  rw [compare_exact]
  split <;> simp only [Square,mul_one,mul_zero]
end ShielddSecurity.BinaryComparison100
