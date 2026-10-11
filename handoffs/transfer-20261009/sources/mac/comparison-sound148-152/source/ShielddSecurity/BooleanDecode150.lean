import ShielddSecurity.CapturedEpochHints62
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BooleanDecode150
open CompilerArithmeticTransport41
variable {F : Type} [Field F]
noncomputable def decoded (xs : List F) : List Bool := by
  classical
  exact xs.map (fun x => decide (x=1))
theorem encode_binary (bits : List Bool) : encodeBits bits.length (binary bits)=bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    have half : (1+2*binary bits)/2=binary bits := by omega
    cases bit <;> simp [encodeBits,binary,ih,half]
theorem decoded_fields (xs : List F) (booleans : ∀ x∈xs,Square x x) :
    (decoded xs).map (fun b => if b then (1:F) else 0)=xs := by
  classical
  apply List.ext_getElem
  · simp [decoded]
  · intro i hi hj
    simp only [decoded,List.getElem_map]
    rcases boolean_sound (xs[i]) (booleans _ (List.getElem_mem hj)) with zero | one
    · simp [zero]
    · simp [one]
theorem decoded_bound (xs : List F) : binary (decoded xs)<2^xs.length := by
  simpa only [decoded,List.length_map] using binary_bound (decoded xs)
theorem decoded_value (xs : List F) (booleans : ∀ x∈xs,Square x x) :
    (binary (decoded xs):F)=fieldBinary xs := by
  rw [←binary_cast,decoded_fields xs booleans]
variable [CharP F p]
theorem canonical_bits (xs : List F) (n : Nat) (bound : 2^xs.length<p)
    (canonical : n<p) (booleans : ∀ x∈xs,Square x x) (meaning : fieldBinary xs=(n:F)) :
    xs=(encodeBits xs.length n).map (fun b => if b then (1:F) else 0) := by
  have exactBound:=Nat.lt_trans (decoded_bound xs) bound
  have same:=CapturedEpochHints62.cast_small_unique (binary (decoded xs)) n exactBound canonical
    ((decoded_value xs booleans).trans meaning)
  have encoded : encodeBits xs.length n=decoded xs := by
    rw [←same]
    simpa only [decoded,List.length_map] using encode_binary (decoded xs)
  rw [encoded,decoded_fields xs booleans]
end ShielddSecurity.BooleanDecode150

set_option pp.all true in
#check @ShielddSecurity.BooleanDecode150.decoded
#print axioms ShielddSecurity.BooleanDecode150.decoded
set_option pp.all true in
#check @ShielddSecurity.BooleanDecode150.encode_binary
#print axioms ShielddSecurity.BooleanDecode150.encode_binary
set_option pp.all true in
#check @ShielddSecurity.BooleanDecode150.decoded_fields
#print axioms ShielddSecurity.BooleanDecode150.decoded_fields
set_option pp.all true in
#check @ShielddSecurity.BooleanDecode150.decoded_bound
#print axioms ShielddSecurity.BooleanDecode150.decoded_bound
set_option pp.all true in
#check @ShielddSecurity.BooleanDecode150.decoded_value
#print axioms ShielddSecurity.BooleanDecode150.decoded_value
set_option pp.all true in
#check @ShielddSecurity.BooleanDecode150.canonical_bits
#print axioms ShielddSecurity.BooleanDecode150.canonical_bits
