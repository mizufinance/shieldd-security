import ShielddSecurity.SDKCompressedDecoder01

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.SDKSignSelection01
open ConcreteJubjubField01

/-- Mathematical reflection of root conditional-negation. ZIP216 rejects
zero root with sign one; native sqrt and canonical byte refinement are separate. -/
def selectRoot (root : F) (sign : Nat) : F :=
  if root.val % 2 = sign then root else -root

theorem selected_square (root : F) (sign : Nat) : (selectRoot root sign) ^ 2 = root ^ 2 := by
  unfold selectRoot
  split <;> simp

theorem selected_sign (root : F) (sign : Nat) (bit : sign < 2)
    (admissible : ¬(root = 0 ∧ sign = 1)) : (selectRoot root sign).val % 2 = sign := by
  by_cases same : root.val % 2 = sign
  · simp only [selectRoot, if_pos same]
    exact same
  · have nonzero : root ≠ 0 := by
      intro zero
      have parity : root.val % 2 = 0 := by simp [zero]
      have one : sign = 1 := by omega
      exact admissible ⟨zero, one⟩
    letI : NeZero root := ⟨nonzero⟩
    simp only [selectRoot, if_neg same, ZMod.val_neg_of_ne_zero]
    have bound := ZMod.val_lt root
    have primeOdd : Scalar.modulus % 2 = 1 := by decide +kernel
    omega

def decodedPoint (y root : F) (sign : Nat) : Group.Point F := ⟨selectRoot root sign, y⟩

theorem selected_decoded (y root : F) (sign : Nat) (bit : sign < 2)
    (admissible : ¬(root = 0 ∧ sign = 1))
    (squareRoot : root ^ 2 = (y ^ 2 - 1) / (1 + coefficient * y ^ 2)) :
    SDKCompressedDecoder01.Decoded y sign (decodedPoint y root sign) := by
  refine ⟨rfl, ?_, selected_sign root sign bit admissible⟩
  exact (selected_square root sign).trans squareRoot

theorem sdk_root_nonzero (root : F)
    (squareRoot : root ^ 2 = ((SDKSpendAuthCertificates01.sdkY : F) ^ 2 - 1) /
      (1 + coefficient * (SDKSpendAuthCertificates01.sdkY : F) ^ 2)) : root ≠ 0 := by
  let candidate : Group.Point F := ⟨root, (SDKSpendAuthCertificates01.sdkY : F)⟩
  have decoded : SDKCompressedDecoder01.Decoded (SDKSpendAuthCertificates01.sdkY : F)
      (root.val % 2) candidate := ⟨rfl, squareRoot, rfl⟩
  have curve := SDKCompressedDecoder01.decoded_on_curve _ _ _ decoded
  have sameY : candidate.y = SDKSpendAuthCertificates01.sdkBase.y := by
    rw [SDKSpendAuthCertificates01.sdk_base_coordinates]
  have denominator := SDKCompressedDecoder01.denominator_nonzero coefficient imaginary
    SDKSpendAuthCertificates01.sdkBase.y coefficient_no_unit_square imaginary_square
  have baseNonzero : SDKSpendAuthCertificates01.sdkBase.x ≠ 0 := by
    intro zero
    have odd := SDKSpendAuthCertificates01.sdk_x_odd
    rw [← SDKCompressedDecoder01.sdk_x_value, zero] at odd
    simp at odd
  rcases SDKCompressedDecoder01.same_y_roots coefficient candidate SDKSpendAuthCertificates01.sdkBase
    curve SDKSpendAuthCertificates01.sdkBase_on_curve sameY denominator with positive | negative
  · change root = SDKSpendAuthCertificates01.sdkBase.x at positive
    rw [positive]
    exact baseNonzero
  · change root = -SDKSpendAuthCertificates01.sdkBase.x at negative
    rw [negative]
    exact neg_ne_zero.mpr baseNonzero

theorem sdk_root_selected (root : F)
    (squareRoot : root ^ 2 = ((SDKSpendAuthCertificates01.sdkY : F) ^ 2 - 1) /
      (1 + coefficient * (SDKSpendAuthCertificates01.sdkY : F) ^ 2)) :
    decodedPoint (SDKSpendAuthCertificates01.sdkY : F) root 1 = SDKSpendAuthCertificates01.sdkBase := by
  apply SDKCompressedDecoder01.sdk_decoded_unique
  exact selected_decoded _ _ _ (by decide)
    (fun rejected => sdk_root_nonzero root squareRoot rejected.1) squareRoot

end ShielddSecurity.SDKSignSelection01


set_option pp.all true in
#check @ShielddSecurity.SDKSignSelection01.selectRoot
#print axioms ShielddSecurity.SDKSignSelection01.selectRoot
set_option pp.all true in
#check @ShielddSecurity.SDKSignSelection01.selected_square
#print axioms ShielddSecurity.SDKSignSelection01.selected_square
set_option pp.all true in
#check @ShielddSecurity.SDKSignSelection01.selected_sign
#print axioms ShielddSecurity.SDKSignSelection01.selected_sign
set_option pp.all true in
#check @ShielddSecurity.SDKSignSelection01.decodedPoint
#print axioms ShielddSecurity.SDKSignSelection01.decodedPoint
set_option pp.all true in
#check @ShielddSecurity.SDKSignSelection01.selected_decoded
#print axioms ShielddSecurity.SDKSignSelection01.selected_decoded
set_option pp.all true in
#check @ShielddSecurity.SDKSignSelection01.sdk_root_nonzero
#print axioms ShielddSecurity.SDKSignSelection01.sdk_root_nonzero
set_option pp.all true in
#check @ShielddSecurity.SDKSignSelection01.sdk_root_selected
#print axioms ShielddSecurity.SDKSignSelection01.sdk_root_selected
