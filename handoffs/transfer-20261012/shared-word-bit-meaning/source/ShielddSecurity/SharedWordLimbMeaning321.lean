import ShielddSecurity.SharedWordBitMeaning320
import ShielddSecurity.LowBitMeaning128
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedWordLimbMeaning321
open Compiler CompilerArithmeticTransport41 WordHints210
variable {F : Type} [Field F] [CharP F p] [DecidableEq F]

theorem encoded_point (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
    (coherent : SharedWordFlags220.Coherent (SharedWordFlags220.assignments SharedWordWitness221.wordSlots numbers))
    (entry : Slot × Nat) (member : entry ∈ CapturedWordRoot213.words)
    (index : Nat) (bound : index < entry.1.width) :
    SharedWordWitness221.completed base numbers fallback (entry.1.start+index) =
      BooleanHints207.bitValue ((encodeBits entry.1.width (numbers entry.1.value))[index]?.getD false) := by
  have equal := congrArg (fun values : List F => values[index]?)
    (SharedWordBitMeaning320.encoded_field base numbers fallback coherent entry member)
  have bits : index < (encodeBits entry.1.width (numbers entry.1.value)).length := by
    rw [encodeBits_length]; exact bound
  simp only [columns,List.getElem?_map,List.getElem?_range' bound,Nat.one_mul,
    List.getElem?_eq_getElem bits,Option.map_some] at equal
  exact (Option.some.inj equal).trans (by rw [List.getElem?_eq_getElem bits,Option.getD_some])

theorem full_field_bits (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
    (coherent : SharedWordFlags220.Coherent (SharedWordFlags220.assignments SharedWordWitness221.wordSlots numbers))
    (entry : Slot × Nat) (member : entry ∈ CapturedWordRoot213.words) (width : entry.1.width=255) :
    ∀ index < 255, SharedWordWitness221.completed base numbers fallback (entry.1.start+index) =
      if (encodeBits 255 (numbers entry.1.value))[index]?.getD false then 1 else 0 := by
  intro index bound
  have point := encoded_point base numbers fallback coherent entry member index (by rw [width]; exact bound)
  rw [width] at point
  exact point

theorem high_window (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
    (coherent : SharedWordFlags220.Coherent (SharedWordFlags220.assignments SharedWordWitness221.wordSlots numbers))
    (entry : Slot × Nat) (member : entry ∈ CapturedWordRoot213.words) (width : entry.1.width=255) :
    (List.range' (entry.1.start+128) 127).map (SharedWordWitness221.completed base numbers fallback) =
      (encodeBits 127 (numbers entry.1.value / 2^128)).map (fun bit => if bit then (1:F) else 0) :=
  HighBitMeaning122.high_map _ entry.1.start (numbers entry.1.value)
    (full_field_bits base numbers fallback coherent entry member width)

theorem low_window (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
    (coherent : SharedWordFlags220.Coherent (SharedWordFlags220.assignments SharedWordWitness221.wordSlots numbers))
    (entry : Slot × Nat) (member : entry ∈ CapturedWordRoot213.words) (width : entry.1.width=255) :
    (List.range' entry.1.start 128).map (SharedWordWitness221.completed base numbers fallback) =
      (encodeBits 128 (numbers entry.1.value)).map (fun bit => if bit then (1:F) else 0) :=
  LowBitMeaning128.low_map _ entry.1.start (numbers entry.1.value)
    (full_field_bits base numbers fallback coherent entry member width)

theorem canonical_low (number : Nat) (bound : number < 2^255) :
    LowBitMeaning128.low number = number % 2^128 := by
  have equal := congrArg (fun value : Nat => value % 2^128) (LowBitMeaning128.recombine number bound)
  dsimp only at equal
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (LowBitMeaning128.low_bound number)] at equal
  exact equal.symm
end ShielddSecurity.SharedWordLimbMeaning321

set_option pp.all true in
#check @ShielddSecurity.SharedWordLimbMeaning321.encoded_point
#print axioms ShielddSecurity.SharedWordLimbMeaning321.encoded_point

set_option pp.all true in
#check @ShielddSecurity.SharedWordLimbMeaning321.full_field_bits
#print axioms ShielddSecurity.SharedWordLimbMeaning321.full_field_bits

set_option pp.all true in
#check @ShielddSecurity.SharedWordLimbMeaning321.high_window
#print axioms ShielddSecurity.SharedWordLimbMeaning321.high_window

set_option pp.all true in
#check @ShielddSecurity.SharedWordLimbMeaning321.low_window
#print axioms ShielddSecurity.SharedWordLimbMeaning321.low_window

set_option pp.all true in
#check @ShielddSecurity.SharedWordLimbMeaning321.canonical_low
#print axioms ShielddSecurity.SharedWordLimbMeaning321.canonical_low
