import ShielddSecurity.ReceiverLifecycleWordSoundness
import Mathlib.Data.List.Basic

set_option maxHeartbeats 200000

namespace ShielddSecurity.ReceiverLifecycleWordShape

/-- Split the actual 131-bit word into status, unconstrained middle and zero
high suffix. Only three low bits are inspected; the high suffix is symbolic. -/
theorem shape (bits : List Bool) (width : bits.length = 131)
    (low : bits.take 3 = [true,false,false])
    (high : ∀ bit ∈ bits.drop 67,bit = false) :
    ∃ middle : List Bool,middle.length = 64 ∧
      bits = [true,false,false] ++ middle ++ List.replicate 64 false := by
  let middle := (bits.drop 3).take 64
  have middleWidth : middle.length = 64 := by
    simp [middle,List.length_take,List.length_drop,width]
  have highWidth : (bits.drop 67).length = 64 := by
    simp [List.length_drop,width]
  have tail : bits.drop 67 = List.replicate 64 false := by
    rw [← highWidth]
    exact List.eq_replicate_length.mpr high
  have doubleDrop : (bits.drop 3).drop 64 = bits.drop 67 := by
    rw [List.drop_drop]
  refine ⟨middle,middleWidth,?_⟩
  calc
    bits = bits.take 3 ++ bits.drop 3 := (List.take_append_drop 3 bits).symm
    _ = [true,false,false] ++ ((bits.drop 3).take 64 ++ (bits.drop 3).drop 64) := by
      rw [low]
      exact congrArg (fun suffix => [true,false,false] ++ suffix)
        (List.take_append_drop 64 (bits.drop 3)).symm
    _ = [true,false,false] ++ middle ++ List.replicate 64 false := by
      rw [doubleDrop,tail]
      rfl

/-- Source gate composition supplies the low/status and high-zero facts on the
same reconstructed Boolean word; they imply the native active predicate. -/
theorem active (bits : List Bool) (width : bits.length = 131)
    (low : bits.take 3 = [true,false,false])
    (high : ∀ bit ∈ bits.drop 67,bit = false) :
    ReceiverLifecycle.LegalActive (binary bits) := by
  obtain ⟨middle,middleWidth,word⟩ := shape bits width low high
  rw [word]
  exact ReceiverLifecycleWordSoundness.active_word middle middleWidth

/-- The range witness is the integer of this same word, so the Boolean gate
consequences imply its native status predicate without a field alias. -/
theorem encoded_active (n : Nat) (bound : n < 2^131)
    (low : (encodeBits 131 n).take 3 = [true,false,false])
    (high : ∀ bit ∈ (encodeBits 131 n).drop 67,bit = false) :
    ReceiverLifecycle.LegalActive n := by
  have result := active (encodeBits 131 n) (encodeBits_length 131 n) low high
  simpa only [encodeBits_value 131 n bound] using result

set_option pp.all true in
#check @shape
#print axioms shape
set_option pp.all true in
#check @active
#print axioms active
set_option pp.all true in
#check @encoded_active
#print axioms encoded_active

end ShielddSecurity.ReceiverLifecycleWordShape
