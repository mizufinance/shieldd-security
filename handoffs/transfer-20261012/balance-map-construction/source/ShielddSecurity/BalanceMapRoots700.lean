import ShielddSecurity.BalanceMapParameters699
import ShielddSecurity.BalanceSquareAlternative702
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceMapRoots700
open ConcreteJubjubField01 BalanceMapParameters699

def normalize (choice : Bool) (root : F) : F :=
  if root.val % 2 = (if choice then 1 else 0) then root else -root

theorem negation_flips (root : F) (nonzero : root≠0) :
    (-root).val % 2 ≠ root.val % 2 := by
  rw [ZMod.neg_val,if_neg nonzero]
  have bounded := root.val_lt
  have positive : 0<root.val := by
    by_contra absent
    exact nonzero ((ZMod.val_eq_zero root).mp (by omega))
  have odd : Scalar.modulus % 2 = 1 := by decide
  omega

theorem normalize_square (choice : Bool) (root : F) : (normalize choice root)^2=root^2 := by
  unfold normalize
  split_ifs <;> simp

theorem normalize_parity (choice : Bool) (root : F) (nonzero : choice=true → root≠0) :
    (normalize choice root).val % 2 = if choice then 1 else 0 := by
  by_cases target : root.val % 2 = (if choice then 1 else 0)
  · simpa [normalize,target] using target
  · rw [normalize,if_neg target]
    by_cases zero : root=0
    · subst root
      cases choice <;> simp_all
    · have flip := negation_flips root zero
      have bounded : root.val % 2 < 2 := Nat.mod_lt _ (by decide)
      have negBound : (-root).val % 2 < 2 := Nat.mod_lt _ (by decide)
      cases choice <;> simp only [Bool.false_eq_true,if_false,if_true] at target ⊢ <;> omega

noncomputable def choice (u : F) : Bool := by
  classical
  exact decide (IsSquare (sourceFirstCubic u))

theorem nonsquare_alternative (value : F) (nonsquare : ¬ IsSquare value) : IsSquare ((5:F)*value) := by
  exact BalanceSquareAlternative702.alternative 5 value
    (exact_negative_euler_parameter_is_nonsquare 5 exact_elligator_five_parameter_has_negative_euler_power) nonsquare

theorem qr_available (u : F) : IsSquare (if choice u then sourceFirstCubic u else 5*sourceFirstCubic u) := by
  classical
  by_cases square : IsSquare (sourceFirstCubic u)
  · simpa only [choice,decide_eq_true square,if_true] using square
  · simpa only [choice,decide_eq_false square,Bool.false_eq_true,if_false] using nonsquare_alternative _ square

noncomputable def qrRoot (u : F) : F := Classical.choose (qr_available u)

theorem qr_square (u : F) : (qrRoot u)^2=if choice u then sourceFirstCubic u else 5*sourceFirstCubic u := by
  simpa only [qrRoot,pow_two] using (Classical.choose_spec (qr_available u)).symm

noncomputable def selectedRoot (u : F) : F :=
  normalize (choice u) (if choice u then qrRoot u else u*qrRoot u)

theorem selected_square (u : F) : (selectedRoot u)^2=
    if choice u then sourceFirstCubic u else 5*u*u*sourceFirstCubic u := by
  rw [selectedRoot,normalize_square]
  cases h : choice u
  · simp only [h,Bool.false_eq_true,if_false]
    rw [mul_pow,qr_square,h]
    simp only [Bool.false_eq_true,if_false]
    ring
  · simpa only [h,if_true] using qr_square u

theorem selected_parity (u : F) : (selectedRoot u).val % 2=if choice u then 1 else 0 := by
  apply normalize_parity
  intro chosen
  simp only [chosen,if_true]
  intro zero
  have square := qr_square u
  apply actual_elligator_first_cubic_is_nonzero u
  simpa [chosen,zero] using square.symm
end ShielddSecurity.BalanceMapRoots700

set_option pp.all true in
#check @ShielddSecurity.BalanceMapRoots700.negation_flips
#print axioms ShielddSecurity.BalanceMapRoots700.negation_flips

set_option pp.all true in
#check @ShielddSecurity.BalanceMapRoots700.normalize_square
#print axioms ShielddSecurity.BalanceMapRoots700.normalize_square

set_option pp.all true in
#check @ShielddSecurity.BalanceMapRoots700.normalize_parity
#print axioms ShielddSecurity.BalanceMapRoots700.normalize_parity

set_option pp.all true in
#check @ShielddSecurity.BalanceMapRoots700.qr_available
#print axioms ShielddSecurity.BalanceMapRoots700.qr_available

set_option pp.all true in
#check @ShielddSecurity.BalanceMapRoots700.qr_square
#print axioms ShielddSecurity.BalanceMapRoots700.qr_square

set_option pp.all true in
#check @ShielddSecurity.BalanceMapRoots700.selected_square
#print axioms ShielddSecurity.BalanceMapRoots700.selected_square

set_option pp.all true in
#check @ShielddSecurity.BalanceMapRoots700.selected_parity
#print axioms ShielddSecurity.BalanceMapRoots700.selected_parity

set_option pp.all true in
#check @ShielddSecurity.BalanceMapRoots700.nonsquare_alternative
#print axioms ShielddSecurity.BalanceMapRoots700.nonsquare_alternative
