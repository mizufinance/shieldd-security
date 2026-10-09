import ShielddSecurity.ScalarBooleanReflection

set_option maxHeartbeats 200000
namespace ShielddSecurity.ScalarBooleanCanonical

theorem encode_binary (bits : List Bool) : encodeBits bits.length (binary bits) = bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      have half : ((if bit then 1 else 0) + 2 * binary bits) / 2 = binary bits := by
        cases bit <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega
      have parity : decide (((if bit then 1 else 0) + 2 * binary bits) % 2 = 1) = bit := by
        cases bit <;> simp [Nat.add_mod]
      change decide (((if bit then 1 else 0) + 2 * binary bits) % 2 = 1) ::
        encodeBits bits.length (((if bit then 1 else 0) + 2 * binary bits) / 2) = bit :: bits
      rw [parity,half,ih]

/-- Boolean row truth fixes every encoded bit, not merely the reduced word. -/
theorem canonical_word {F : Type} [Field F] (xs : List F)
    (booleans : ∀ x ∈ xs, Square x x) :
    ∃ n : Nat, n < 2 ^ xs.length ∧ fieldBinary xs = (n : F) ∧
      xs = (encodeBits xs.length n).map (fun bit => if bit then (1 : F) else 0) := by
  classical
  let bits := xs.map (fun x => decide (x = 1))
  have values : xs = bits.map (fun bit => if bit then (1 : F) else 0) := by
    change xs = (xs.map (fun x => decide (x = 1))).map _
    rw [List.map_map]
    conv_lhs => rw [← List.map_id xs]
    apply List.map_congr_left
    intro x member
    rcases boolean_sound x (booleans x member) with zero | one
    · simp [zero]
    · simp [one]
  refine ⟨binary bits,?_,?_,?_⟩
  · simpa only [bits,List.length_map] using binary_bound bits
  · rw [values]; exact binary_cast bits
  · have length : bits.length = xs.length := by simp only [bits,List.length_map]
    rw [← length,encode_binary]
    exact values

theorem columns_word {F : Type} [Field F] (rho : Nat → F)
    (columns : List Nat) (value : Nat)
    (booleans : Satisfies rho (columns.map booleanRow))
    (reconstruction : Square (eval rho (reconstructionRow value columns).a)
      (eval rho (reconstructionRow value columns).b)) :
    ∃ n : Nat, n < 2 ^ columns.length ∧ (n : F) = rho value ∧
      columns.map rho = (encodeBits columns.length n).map (fun bit => if bit then (1 : F) else 0) := by
  have truth : ∀ x ∈ columns.map rho, Square x x := by
    intro x member
    obtain ⟨column,present,rfl⟩ := List.mem_map.mp member
    have row := booleans (booleanRow column) (List.mem_map.mpr ⟨column,present,rfl⟩)
    simpa only [booleanRow,eval,Int.cast_one,one_mul,mul_zero,add_zero] using row
  obtain ⟨n,bound,meaning,word⟩ := canonical_word (columns.map rho) truth
  -- Reconstruct the field word directly, rather than equating bounded naturals
  -- by an unstated characteristic bound.
  have weighted (items : List Nat) (weight : Int) :
      eval rho (weighted items weight) = (weight : F) * fieldBinary (items.map rho) := by
    induction items generalizing weight with
    | nil => simp [ShielddSecurity.weighted,eval,fieldBinary]
    | cons item items ih =>
        simp only [ShielddSecurity.weighted,eval,List.map_cons,fieldBinary,ih,Int.cast_mul,Int.cast_ofNat]
        ring
  have zero := square_zero _ reconstruction
  simp only [reconstructionRow,eval,Int.cast_neg,Int.cast_one,neg_one_mul,weighted,one_mul] at zero
  refine ⟨n,by simpa only [List.length_map] using bound,?_,?_⟩
  · rw [← meaning]
    apply sub_eq_zero.mp
    calc
      fieldBinary (columns.map rho) - rho value = -rho value + fieldBinary (columns.map rho) := by ring
      _ = 0 := zero
  · simpa only [List.length_map] using word

set_option pp.all true in
#check @encode_binary
#print axioms encode_binary
set_option pp.all true in
#check @canonical_word
#print axioms canonical_word
set_option pp.all true in
#check @columns_word
#print axioms columns_word
end ShielddSecurity.ScalarBooleanCanonical
