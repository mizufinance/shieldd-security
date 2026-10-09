import ShielddSecurity.ScalarCompletion
import ShielddSecurity.ScalarWrittenBitValues

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.ReceiverLifecycle

def LegalActive (n : Nat) : Prop := n % 8 = 1 ∧ n < 2^67
def GateIndex (index : Nat) : Prop :=
  index = 0 ∨ index = 1 ∨ index = 2 ∨ (67 ≤ index ∧ index < 131)

theorem encoded_bit (width n index : Nat) (bound : index < width) :
    (encodeBits width n)[index]?.getD false = decide ((n / 2^index) % 2 = 1) := by
  induction index generalizing width n with
  | zero =>
      cases width with
      | zero => omega
      | succ width => simp [encodeBits]
  | succ index ih =>
      cases width with
      | zero => omega
      | succ width =>
          have tail := ih width (n / 2) (by omega)
          simpa [encodeBits, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm] using tail

theorem active_status_bit (n index : Nat) (legal : LegalActive n) (shape : GateIndex index) :
    (encodeBits 131 n)[index]?.getD false = decide (index = 0) := by
  rcases shape with low | second | third | high
  · subst index
    rw [encoded_bit 131 n 0 (by decide)]
    have odd : n % 2 = 1 := by have status := legal.1; omega
    simp [odd]
  · subst index
    rw [encoded_bit 131 n 1 (by decide)]
    have even : (n / 2) % 2 ≠ 1 := by have status := legal.1; omega
    simp [even]
  · subst index
    rw [encoded_bit 131 n 2 (by decide)]
    have even : (n / 4) % 2 ≠ 1 := by have status := legal.1; omega
    simp [even]
  · have certificate : (List.range' 67 64).all (fun i => decide (2^67 ≤ 2^i)) = true := by decide
    have member : index ∈ List.range' 67 64 := by
      exact List.mem_range'.mpr ⟨index-67, by omega, by simp only [Nat.one_mul]; omega⟩
    have power : 2^67 ≤ 2^index :=
      of_decide_eq_true ((List.all_eq_true.mp certificate) index member)
    have small : n < 2^index := lt_of_lt_of_le legal.2 power
    have divided : n / 2^index = 0 := Nat.div_eq_of_lt small
    have nonzero : index ≠ 0 := by omega
    rw [encoded_bit 131 n index high.2]
    simp [divided, nonzero]

theorem enabled_product {F : Type} [Field F] (n index : Nat) (flag : Bool)
    (shape : GateIndex index) (legal : flag = true → LegalActive n) :
    (if flag then (1 : F) else 0) *
      ((if (encodeBits 131 n)[index]?.getD false then (1 : F) else 0) -
       (if index = 0 then 1 else 0)) = 0 := by
  cases flag with
  | false => simp
  | true =>
      rw [active_status_bit n index (legal rfl) shape]
      by_cases first : index = 0 <;> simp [first]

def zeroRows (left right : Linear) (auxiliary : Nat) : List Row :=
  [⟨Compiler.subtract left right, [(auxiliary,1)]⟩,
   ⟨left ++ right, [(auxiliary,1)]⟩]

def extendZero {F : Type} [Field F] (base : Nat → F)
    (left right : Linear) (auxiliary : Nat) : Nat → F :=
  patchAssignment base (fun _ => (eval base left - eval base right)^2) [auxiliary]

theorem zero_preserves {F : Type} [Field F] (base : Nat → F)
    (left right : Linear) (auxiliary column : Nat) (outside : column ≠ auxiliary) :
    extendZero base left right auxiliary column = base column :=
  patchAssignment_preserves base _ [auxiliary] column (by simpa only [List.mem_singleton] using outside)

theorem zero_complete {F : Type} [Field F] (base : Nat → F)
    (left right : Linear) (auxiliary : Nat)
    (fresh : ∀ term ∈ left ++ right, term.1 ≠ auxiliary)
    (legal : eval base left * eval base right = 0) :
    Satisfies (extendZero base left right auxiliary) (zeroRows left right auxiliary) := by
  let rho := extendZero base left right auxiliary
  have agrees (terms : Linear) (included : ∀ term ∈ terms, term ∈ left ++ right) :
      eval rho terms = eval base terms := by
    apply eval_agrees
    intro term member
    exact zero_preserves base left right auxiliary term.1 (fresh term (included term member))
  have leftValue := agrees left (by intro term member; exact List.mem_append_left right member)
  have rightValue := agrees right (by intro term member; exact List.mem_append_right left member)
  have auxiliaryValue : rho auxiliary = (eval base left - eval base right)^2 := by
    simp [rho, extendZero, patchAssignment]
  intro row member
  simp only [zeroRows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · change Square (eval rho (Compiler.subtract left right)) (eval rho [(auxiliary,1)])
    rw [Compiler.eval_subtract,leftValue,rightValue]
    simp only [eval,Int.cast_one,one_mul,add_zero,auxiliaryValue,Square,pow_two]
  · change Square (eval rho (left ++ right)) (eval rho [(auxiliary,1)])
    rw [eval_append,leftValue,rightValue]
    simp only [eval,Int.cast_one,one_mul,add_zero,auxiliaryValue,Square,pow_two]
    calc
      (eval base left + eval base right) * (eval base left + eval base right) =
          (eval base left - eval base right) * (eval base left - eval base right) +
            4 * (eval base left * eval base right) := by ring
      _ = (eval base left - eval base right) * (eval base left - eval base right) := by rw [legal]; ring

set_option pp.all true in
#check @encoded_bit
#print axioms encoded_bit
set_option pp.all true in
#check @active_status_bit
#print axioms active_status_bit
set_option pp.all true in
#check @enabled_product
#print axioms enabled_product
set_option pp.all true in
#check @zero_preserves
#print axioms zero_preserves
set_option pp.all true in
#check @zero_complete
#print axioms zero_complete

end ShielddSecurity.ReceiverLifecycle
