import ShielddSecurity.TransferBlstByteRoundtrip01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmCarryChains01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)

/-- Arithmetic view of the locked ARM64 ADDS/ADCS chain, not an ISA execution theorem. -/
def sourceAddCarry (a b : UInt64) (carry : Bool) : UInt64 × Bool :=
  let sum := a.toNat+b.toNat+carry.toNat
  (UInt64.ofNat sum,decide (radix64 ≤ sum))

theorem actual_two_operand_add_with_carry_fits_less_than_two_radices
    (a b : UInt64) (carry : Bool) : a.toNat+b.toNat+carry.toNat < radix64+radix64 := by
  have aBound : a.toNat < radix64 := a.toNat_lt
  have bBound : b.toNat < radix64 := b.toNat_lt
  cases carry with
  | false => change a.toNat+b.toNat+0 < radix64+radix64; omega
  | true => change a.toNat+b.toNat+1 < radix64+radix64; omega

theorem actual_add_carry_arithmetic_conserves_the_full_integer
    (a b : UInt64) (carry : Bool) :
    (sourceAddCarry a b carry).1.toNat+radix64*(sourceAddCarry a b carry).2.toNat =
      a.toNat+b.toNat+carry.toNat := by
  have bound := actual_two_operand_add_with_carry_fits_less_than_two_radices a b carry
  let sum := a.toNat+b.toNat+carry.toNat
  have quotient : sum/radix64 = (decide (radix64 ≤ sum) : Bool).toNat := by
    by_cases overflow : radix64 ≤ sum
    · have one : sum/radix64=1 := by unfold sum radix64 at *; omega
      simp [one,overflow]
    · have low : sum < radix64 := by omega
      simp [Nat.div_eq_of_lt low,overflow]
  change sum % radix64 + radix64*(decide (radix64 ≤ sum) : Bool).toNat = sum
  rw [← quotient]
  exact Nat.mod_add_div sum radix64

def sourceAddCarryChain (carry : Bool) : List (UInt64 × UInt64) → List UInt64 × Bool
  | [] => ([],carry)
  | pair::rest =>
      let step := sourceAddCarry pair.1 pair.2 carry
      let after := sourceAddCarryChain step.2 rest
      (step.1::after.1,after.2)

theorem actual_add_chain_retains_the_source_limb_count
    (carry : Bool) (pairs : List (UInt64 × UInt64)) :
    (sourceAddCarryChain carry pairs).1.length = pairs.length := by
  induction pairs generalizing carry with
  | nil => rfl
  | cons pair rest ih =>
    change (sourceAddCarryChain (sourceAddCarry pair.1 pair.2 carry).2 rest).1.length+1 = rest.length+1
    rw [ih]

theorem symbolic_actual_add_chain_conserves_the_limb_integer_and_final_flag
    (carry : Bool) (pairs : List (UInt64 × UInt64)) :
    packWords (sourceAddCarryChain carry pairs).1+
      radix64^pairs.length*(sourceAddCarryChain carry pairs).2.toNat =
      packWords (pairs.map Prod.fst)+packWords (pairs.map Prod.snd)+carry.toNat := by
  induction pairs generalizing carry with
  | nil => simp only [sourceAddCarryChain,packWords,List.length_nil,List.map_nil,Nat.pow_zero,
      Nat.one_mul,Nat.zero_add]
  | cons pair rest ih =>
    let step := sourceAddCarry pair.1 pair.2 carry
    let after := sourceAddCarryChain step.2 rest
    have tail := ih step.2
    have first := actual_add_carry_arithmetic_conserves_the_full_integer pair.1 pair.2 carry
    change step.1.toNat+radix64*packWords after.1+radix64^(rest.length+1)*after.2.toNat =
      (pair.1.toNat+radix64*packWords (rest.map Prod.fst))+
      (pair.2.toNat+radix64*packWords (rest.map Prod.snd))+carry.toNat
    calc
      _ = step.1.toNat+radix64*(packWords after.1+radix64^rest.length*after.2.toNat) := by
        rw [Nat.pow_succ]; ring
      _ = step.1.toNat+radix64*(packWords (rest.map Prod.fst)+packWords (rest.map Prod.snd)+step.2.toNat) := by rw [tail]
      _ = (step.1.toNat+radix64*step.2.toNat)+
          radix64*packWords (rest.map Prod.fst)+radix64*packWords (rest.map Prod.snd) := by ring
      _ = _ := by rw [first]; ring
set_option pp.all true in
#check @sourceAddCarry
#print axioms sourceAddCarry
set_option pp.all true in
#check @actual_two_operand_add_with_carry_fits_less_than_two_radices
#print axioms actual_two_operand_add_with_carry_fits_less_than_two_radices
set_option pp.all true in
#check @actual_add_carry_arithmetic_conserves_the_full_integer
#print axioms actual_add_carry_arithmetic_conserves_the_full_integer
set_option pp.all true in
#check @sourceAddCarryChain
#print axioms sourceAddCarryChain
set_option pp.all true in
#check @actual_add_chain_retains_the_source_limb_count
#print axioms actual_add_chain_retains_the_source_limb_count
set_option pp.all true in
#check @symbolic_actual_add_chain_conserves_the_limb_integer_and_final_flag
#print axioms symbolic_actual_add_chain_conserves_the_limb_integer_and_final_flag
end ShielddSecurity.TransferBlstArmCarryChains01
