import ShielddSecurity.Range
import ShielddSecurity.Rows
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.HighBitMeaning122
variable {F : Type} [Field F]
theorem encode_drop (width offset n : Nat) :
    (encodeBits (width+offset) n).drop offset=encodeBits width (n/2^offset) := by
  induction offset generalizing n with
  | zero => simp
  | succ offset ih =>
    have count : width+(offset+1)=(width+offset)+1 := by omega
    rw [count,encodeBits,List.drop_succ_cons,ih]
    congr 1
    simp only [Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm]
theorem high_bound (n : Nat) (bound : n<2^255) : n/2^128<2^127 := by
  apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
  simpa only [← Nat.pow_add] using bound
theorem bits_map (rho : Nat → F) (start n : Nat)
    (bits : ∀ index<255,rho (start+index)=if (encodeBits 255 n)[index]?.getD false then 1 else 0) :
    (List.range' start 255).map rho=(encodeBits 255 n).map (fun bit => if bit then (1:F) else 0) := by
  apply List.ext_getElem
  · simp
  · intro index hi hj
    have before : index<255 := by simpa using hi
    simp only [List.getElem_map,List.getElem_range',Nat.mul_one]
    rw [bits index before]
    rw [List.getElem?_eq_getElem (by simpa using before),Option.getD_some]
theorem high_map (rho : Nat → F) (start n : Nat)
    (bits : ∀ index<255,rho (start+index)=if (encodeBits 255 n)[index]?.getD false then 1 else 0) :
    (List.range' (start+128) 127).map rho=
      (encodeBits 127 (n/2^128)).map (fun bit => if bit then (1:F) else 0) := by
  have h:=congrArg (List.drop 128) (bits_map rho start n bits)
  rw [List.drop_map,List.drop_range',List.drop_map,encode_drop 127 128 n] at h
  simpa only [Nat.mul_one] using h
theorem high_meaning (rho : Nat → F) (start n : Nat) (bound : n<2^255)
    (bits : ∀ index<255,rho (start+index)=if (encodeBits 255 n)[index]?.getD false then 1 else 0) :
    fieldBinary ((List.range' (start+128) 127).map rho)=(n/2^128:F) := by
  rw [high_map rho start n bits,binary_cast,encodeBits_value 127 _ (high_bound n bound)]
end ShielddSecurity.HighBitMeaning122
