import ShielddSecurity.SharedRegisteredGeneral308
import ShielddSecurity.LegalWordNormalization272
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedWordBitMeaning320
open WordHints210 Compiler CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p] [DecidableEq F]

theorem bit_column (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
    (entry : Slot × Nat) (member : entry ∈ CapturedWordRoot213.words) (column : Nat)
    (inside : column ∈ columns entry.1) :
    SharedWordWitness221.completed base numbers fallback column =
      BooleanHints207.bitValue (SharedWordWitness221.bits numbers fallback column) := by
  have bounds := (CapturedWordRoot213.originals entry member).1
  obtain ⟨offset,before,equal⟩ := List.mem_range'.mp inside
  simp only [Nat.one_mul] at equal
  exact (SharedRegisteredGeneral308.candidate_original _ column (by omega) (by omega)).trans
    (BooleanHints207.seeded_selected base _ _ column (SharedWordWitness221.word_coverage entry member column inside))

theorem encoded_field (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
    (coherent : SharedWordFlags220.Coherent (SharedWordFlags220.assignments SharedWordWitness221.wordSlots numbers))
    (entry : Slot × Nat) (member : entry ∈ CapturedWordRoot213.words) :
    (columns entry.1).map (SharedWordWitness221.completed base numbers fallback) =
      (encodeBits entry.1.width (numbers entry.1.value)).map (fun bit => BooleanHints207.bitValue (F:=F) bit) := by
  calc
    _ = (columns entry.1).map (fun column => BooleanHints207.bitValue (SharedWordWitness221.bits numbers fallback column)) := by
      apply List.map_congr_left
      intro column inside
      exact bit_column base numbers fallback entry member column inside
    _ = ((columns entry.1).map (SharedWordWitness221.bits numbers fallback)).map (fun bit => BooleanHints207.bitValue (F:=F) bit) := by
      simp only [List.map_map]
      rfl
    _ = _ := congrArg (fun bits : List Bool => bits.map (fun bit => BooleanHints207.bitValue (F:=F) bit))
      (SharedWordWitness221.encoded numbers fallback coherent entry member)

theorem normalized_field (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
    (entry : Slot × Nat) (member : entry ∈ CapturedWordRoot213.words) :
    (columns entry.1).map (SharedWordWitness221.completed base (LegalWordNormalization272.normalized numbers) fallback) =
      (encodeBits entry.1.width (LegalWordNormalization272.normalized numbers entry.1.value)).map
        (fun bit => BooleanHints207.bitValue (F:=F) bit) :=
  encoded_field base _ fallback (LegalWordNormalization272.coherent numbers) entry member
end ShielddSecurity.SharedWordBitMeaning320

set_option pp.all true in
#check @ShielddSecurity.SharedWordBitMeaning320.bit_column
#print axioms ShielddSecurity.SharedWordBitMeaning320.bit_column

set_option pp.all true in
#check @ShielddSecurity.SharedWordBitMeaning320.encoded_field
#print axioms ShielddSecurity.SharedWordBitMeaning320.encoded_field

set_option pp.all true in
#check @ShielddSecurity.SharedWordBitMeaning320.normalized_field
#print axioms ShielddSecurity.SharedWordBitMeaning320.normalized_field
