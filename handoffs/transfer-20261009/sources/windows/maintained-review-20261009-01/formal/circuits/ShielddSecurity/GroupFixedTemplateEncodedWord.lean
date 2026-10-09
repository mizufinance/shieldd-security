import ShielddSecurity.GroupFixedTemplateScalarDigits

set_option maxHeartbeats 100000

namespace ShielddSecurity.GroupFixedTemplateEncodedWord

/-- Recover the whole source bit word from its ascending, in-bounds indices.
This is independent of curve coordinates and of any proposed output. -/
theorem indexed_word (bits : List Bool) :
    (List.range bits.length).map (fun index => bits[index]?.getD false) = bits := by
  apply List.ext_getElem
  · simp
  · intro index leftBound rightBound
    simp only [List.getElem_map, List.getElem_range]
    simp [List.getElem?_eq_getElem rightBound]

theorem encoded_word (width n : Nat) :
    (List.range width).map (fun index => (encodeBits width n)[index]?.getD false) =
      encodeBits width n := by
  simpa only [encodeBits_length] using indexed_word (encodeBits width n)

set_option pp.all true in
#check @indexed_word
#print axioms indexed_word
set_option pp.all true in
#check @encoded_word
#print axioms encoded_word

end ShielddSecurity.GroupFixedTemplateEncodedWord
