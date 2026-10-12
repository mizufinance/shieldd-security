import ShielddSecurity.TransferFfActiveScan01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCommonwareSqrtSearch01
variable {F : Type} [Field F] [DecidableEq F]

/-- Bounded interpretation of the actual Commonware search: test the current
power, square and increment, then refuse if the increment reaches m. The fuel
only bounds traversal; the theorem derives that successful search stays inside it. -/
def searchWalk (m : Nat) : Nat → Nat → F → Option Nat
  | 0,_,_ => none
  | fuel+1,i,t =>
    if t = 1 then some i
    else if i+1 = m then none
    else searchWalk m fuel (i+1) (t*t)

def sourceSearch (m : Nat) (t : F) : Option Nat := searchWalk m m 0 t

theorem repeated_square_search_derives_the_first_power_index
    (b : F) (m k fuel i : Nat) (inside : k < m) (atOrBefore : i ≤ k)
    (fuelBound : k-i < fuel) (power : b ^ (2^k) = 1)
    (earlier : ∀ j : Nat, j < k → b ^ (2^j) ≠ 1) :
    searchWalk m fuel i (b ^ (2^i)) = some k := by
  induction fuel generalizing i with
  | zero => omega
  | succ fuel ih =>
    by_cases reached : i = k
    · simp [searchWalk,reached,power]
    · have before : i < k := by omega
      have different : i+1 ≠ m := by omega
      rw [searchWalk,if_neg (earlier i before),if_neg different]
      have squared : b ^ (2^i) * b ^ (2^i) = b ^ (2^(i+1)) := by
        rw [← pow_two,← pow_mul,← Nat.pow_succ]
      rw [squared]
      exact ih (i+1) (by omega) (by omega)

theorem actual_commonware_search_derives_the_least_positive_exponent
    (b : F) (m : Nat) (active : 1 < m) (bound : b ^ (2^(m-1)) = 1) (nonunit : b ≠ 1) :
    sourceSearch m b = some (TransferFfLeastPower01.leastPositiveExponent b m active bound) := by
  have spec := TransferFfLeastPower01.derived_least_positive_exponent_has_exact_search_bounds_and_power b m active bound
  have earlier : ∀ j : Nat, j < TransferFfLeastPower01.leastPositiveExponent b m active bound → b ^ (2^j) ≠ 1 := by
    intro j before
    by_cases zero : j = 0
    · simpa only [zero,pow_zero,pow_one] using nonunit
    · exact TransferFfLeastPower01.every_earlier_positive_power_before_the_derived_index_is_not_one
        b m active bound j (by omega) before
  simpa only [sourceSearch,pow_zero,pow_one,Nat.sub_zero] using
    repeated_square_search_derives_the_first_power_index b m
      (TransferFfLeastPower01.leastPositiveExponent b m active bound) m 0 spec.2.1 (by omega)
      (by simpa only [Nat.sub_zero] using spec.2.1) spec.2.2 earlier

def squareWalk : Nat → F → F
  | 0,value => value
  | count+1,value => squareWalk count (value*value)

omit [DecidableEq F] in
theorem actual_commonware_correction_walk_has_the_exact_power (count : Nat) (value : F) :
    squareWalk count value = value ^ (2^count) := by
  induction count generalizing value with
  | zero => simp [squareWalk]
  | succ count ih =>
    rw [squareWalk,ih,← pow_two,← pow_mul]
    congr 1
    rw [Nat.pow_succ,Nat.mul_comm]

set_option pp.all true in
#check @searchWalk
#print axioms searchWalk
set_option pp.all true in
#check @sourceSearch
#print axioms sourceSearch
set_option pp.all true in
#check @repeated_square_search_derives_the_first_power_index
#print axioms repeated_square_search_derives_the_first_power_index
set_option pp.all true in
#check @actual_commonware_search_derives_the_least_positive_exponent
#print axioms actual_commonware_search_derives_the_least_positive_exponent
set_option pp.all true in
#check @squareWalk
#print axioms squareWalk
set_option pp.all true in
#check @actual_commonware_correction_walk_has_the_exact_power
#print axioms actual_commonware_correction_walk_has_the_exact_power
end ShielddSecurity.TransferCommonwareSqrtSearch01
