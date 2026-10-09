import ShielddSecurity.RoutingNativeWord

set_option maxHeartbeats 300000

namespace ShielddSecurity.RoutingWordEquality

/-- Symbolic bitvector extensionality avoids enumerating the 32 tag bits. -/
theorem bounded_bit_injective (left right : Nat) (leftBound : left < 2 ^ 32)
    (rightBound : right < 2 ^ 32)
    (bits : ∀ bit : Fin 32, decide (left / 2 ^ bit.val % 2 = 1) =
      decide (right / 2 ^ bit.val % 2 = 1)) : left = right := by
  have words : BitVec.ofNat 32 left = BitVec.ofNat 32 right := by
    apply BitVec.eq_of_getLsbD_eq
    intro index within
    simpa only [BitVec.getLsbD_ofNat, within, decide_true, Bool.true_and,
      Nat.testBit_eq_decide_div_mod_eq] using bits ⟨index, within⟩
  have values := congrArg BitVec.toNat words
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt leftBound,
    Nat.mod_eq_of_lt rightBound] using values

/-- The final integer equality follows from separately certified circuit bit
equations and the native word formula. The caller still owns those equations. -/
theorem selected_word_unique (tag : Nat) (tagBound : tag < 2 ^ 32)
    (meaningful : Bool) (precision : Nat) (route random : BitVec 32)
    (bits : ∀ bit : Fin 32, decide (tag / 2 ^ bit.val % 2 = 1) =
      if meaningful && decide (bit.val < precision)
      then decide (route.toNat / 2 ^ bit.val % 2 = 1)
      else decide (random.toNat / 2 ^ bit.val % 2 = 1)) :
    tag = (RoutingNativeWord.word meaningful precision route random).toNat := by
  have native := RoutingNativeWord.word_semantics meaningful precision route random
  apply bounded_bit_injective tag _ tagBound native.1
  intro bit
  exact (bits bit).trans (native.2 bit).symm

set_option pp.all true in
#check @bounded_bit_injective
#print axioms bounded_bit_injective
set_option pp.all true in
#check @selected_word_unique
#print axioms selected_word_unique

end ShielddSecurity.RoutingWordEquality
