import ShielddSecurity.TransferProjection

set_option maxHeartbeats 150000

namespace ShielddSecurity.TransferFeeAccounting

/-! Independent arithmetic of the owned fee path. A payment retains the same
public fee and native computed base fee. The native pay_fee comparison is a
local guard, not a conservation hypothesis. Mathematical and wrapping totals
are separate definitions. The Rust decoder, arithmetic profile, successful
pay_fee sequence, object-state reset and Host/proposal count correspondence
remain source/refinement obligations. No overflow bound is a setup contract. -/

structure Payment where
  paid : Nat
  base : Nat

def Payment.tip (payment : Payment) : Nat := payment.paid - payment.base

structure Accumulator where
  base : Nat
  tip : Nat

def totals : List Payment → Accumulator
  | [] => ⟨0, 0⟩
  | payment :: rest =>
      ⟨payment.base + (totals rest).base, payment.tip + (totals rest).tip⟩

def paidTotal : List Payment → Nat
  | [] => 0
  | payment :: rest => payment.paid + paidTotal rest

-- The nil case normalizes the initial value. For the actual zero-start state
-- and canonical intermediate values this normalization changes nothing.
def wrappingFrom (width : Nat) (initial : Accumulator) : List Payment → Accumulator
  | [] => ⟨initial.base % width, initial.tip % width⟩
  | payment :: rest => wrappingFrom width
      ⟨(initial.base + payment.base) % width,
        (initial.tip + payment.tip) % width⟩ rest

def checkedAdd (width left right : Nat) : Option Nat :=
  if left + right < width then some (left + right) else none

theorem payment_split (payment : Payment) (guard : payment.base ≤ payment.paid) :
    payment.base + payment.tip = payment.paid := by
  exact Nat.add_sub_of_le guard

theorem totals_split (payments : List Payment)
    (guards : ∀ payment ∈ payments, payment.base ≤ payment.paid) :
    (totals payments).base + (totals payments).tip = paidTotal payments := by
  induction payments with
  | nil => rfl
  | cons payment rest ih =>
      have first := payment_split payment (guards payment (List.mem_cons_self ..))
      have tail := ih (fun next inside => guards next (List.mem_cons_of_mem _ inside))
      simp only [totals, paidTotal]
      omega

theorem wrapping_totals (width : Nat) (initial : Accumulator) (payments : List Payment) :
    (wrappingFrom width initial payments).base =
      (initial.base + (totals payments).base) % width ∧
    (wrappingFrom width initial payments).tip =
      (initial.tip + (totals payments).tip) % width := by
  induction payments generalizing initial with
  | nil => exact ⟨rfl, rfl⟩
  | cons payment rest ih =>
      obtain ⟨base, tip⟩ := ih
        ⟨(initial.base + payment.base) % width, (initial.tip + payment.tip) % width⟩
      constructor
      · simpa only [wrappingFrom, totals, Nat.mod_add_mod, Nat.add_assoc] using base
      · simpa only [wrappingFrom, totals, Nat.mod_add_mod, Nat.add_assoc] using tip

theorem wrapping_paid_total (width : Nat) (payments : List Payment)
    (guards : ∀ payment ∈ payments, payment.base ≤ payment.paid) :
    ((wrappingFrom width ⟨0, 0⟩ payments).base +
      (wrappingFrom width ⟨0, 0⟩ payments).tip) % width = paidTotal payments % width := by
  obtain ⟨base, tip⟩ := wrapping_totals width ⟨0, 0⟩ payments
  simp only [Nat.zero_add] at base tip
  rw [base, tip, ← Nat.add_mod, totals_split payments guards]

theorem checked_success (width left right value : Nat)
    (success : checkedAdd width left right = some value) :
    value = left + right ∧ left + right < width := by
  unfold checkedAdd at success
  split at success
  · rename_i bounded
    have same := Option.some.inj success
    exact ⟨same.symm, bounded⟩
  · cases success

theorem checked_overflow (width left right : Nat) (overflow : width ≤ left + right) :
    checkedAdd width left right = none := by
  simp only [checkedAdd, if_neg (Nat.not_lt.mpr overflow)]

theorem base_total_bound (payments : List Payment) (bound : Nat)
    (bounds : ∀ payment ∈ payments, payment.base ≤ bound) :
    (totals payments).base ≤ payments.length * bound := by
  induction payments with
  | nil => simp only [totals, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons payment rest ih =>
      have first := bounds payment (List.mem_cons_self ..)
      have tail := ih (fun next inside => bounds next (List.mem_cons_of_mem _ inside))
      simp only [totals, List.length_cons, Nat.succ_mul]
      omega

theorem proposal_base_capacity (payments : List Payment)
    (count : payments.length ≤ 4096)
    (native_width : ∀ payment ∈ payments, payment.base ≤ 2 ^ 64 - 1) :
    (totals payments).base < 2 ^ 128 := by
  have bounded := base_total_bound payments (2 ^ 64 - 1) native_width
  have count_bound := Nat.mul_le_mul_right (2 ^ 64 - 1) count
  have capacity : 4096 * (2 ^ 64 - 1) < 2 ^ 128 := by decide
  exact Nat.lt_of_le_of_lt (Nat.le_trans bounded count_bound) capacity

theorem max_price_transfer_product : (2 ^ 64 - 1) * 4000 ≥ 2 ^ 64 := by
  decide

theorem single_maximum_tip_exceeds_base_count_bound :
    (2 ^ 128 - 1) - 0 > 4096 * (2 ^ 64 - 1) := by
  decide

set_option pp.all true in
#check @payment_split
#print axioms payment_split
set_option pp.all true in
#check @totals_split
#print axioms totals_split
set_option pp.all true in
#check @wrapping_totals
#print axioms wrapping_totals
set_option pp.all true in
#check @wrapping_paid_total
#print axioms wrapping_paid_total
set_option pp.all true in
#check @checked_success
#print axioms checked_success
set_option pp.all true in
#check @checked_overflow
#print axioms checked_overflow
set_option pp.all true in
#check @base_total_bound
#print axioms base_total_bound
set_option pp.all true in
#check @proposal_base_capacity
#print axioms proposal_base_capacity
set_option pp.all true in
#check @max_price_transfer_product
#print axioms max_price_transfer_product
set_option pp.all true in
#check @single_maximum_tip_exceeds_base_count_bound
#print axioms single_maximum_tip_exceeds_base_count_bound

end ShielddSecurity.TransferFeeAccounting
