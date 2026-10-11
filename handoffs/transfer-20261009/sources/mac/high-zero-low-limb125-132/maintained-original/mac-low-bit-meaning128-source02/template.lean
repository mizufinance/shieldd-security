import ShielddSecurity.HighBitMeaning122
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.LowBitMeaning128
variable {F : Type} [Field F]
def low (n : Nat) : Nat := binary (encodeBits 128 n)
theorem binary_append (left right : List Bool) :
    binary (left++right)=binary left+2^left.length*binary right := by
  induction left with
  | nil => simp [binary]
  | cons bit left ih =>
    simp only [List.cons_append,binary,List.length_cons,Nat.pow_succ,ih]
    ring
theorem encode_take (width rest n : Nat) :
    (encodeBits (width+rest) n).take width=encodeBits width n := by
  induction width generalizing n with
  | zero => rfl
  | succ width ih =>
    have count : (width+1)+rest=(width+rest)+1 := by omega
    rw [count,encodeBits,List.take_succ_cons,ih]
    rfl
theorem low_bound (n : Nat) : low n<2^128 := by
  simpa only [low,encodeBits_length] using binary_bound (encodeBits 128 n)
theorem low_map (rho : Nat → F) (start n : Nat)
    (bits : ∀ index<255,rho (start+index)=if (encodeBits 255 n)[index]?.getD false then 1 else 0) :
    (List.range' start 128).map rho=(encodeBits 128 n).map (fun bit => if bit then (1:F) else 0) := by
  have h:=congrArg (List.take 128) (HighBitMeaning122.bits_map rho start n bits)
  rw [← List.map_take,List.take_range'_of_length_ge (by decide),← List.map_take,encode_take 128 127 n] at h
  exact h
theorem low_meaning (rho : Nat → F) (start n : Nat)
    (bits : ∀ index<255,rho (start+index)=if (encodeBits 255 n)[index]?.getD false then 1 else 0) :
    fieldBinary ((List.range' start 128).map rho)=(low n:F) := by
  rw [low_map rho start n bits,binary_cast]
  rfl
theorem recombine (n : Nat) (bound : n<2^255) : n=low n+2^128*(n/2^128) := by
  have h:=binary_append ((encodeBits 255 n).take 128) ((encodeBits 255 n).drop 128)
  rw [List.take_append_drop,encodeBits_value 255 n bound,encode_take 128 127 n,
    HighBitMeaning122.encode_drop 127 128 n,encodeBits_length,
    encodeBits_value 127 _ (HighBitMeaning122.high_bound n bound)] at h
  exact h
end ShielddSecurity.LowBitMeaning128
