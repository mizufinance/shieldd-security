import ShielddSecurity.CompilerZeroTest65
import ShielddSecurity.CapturedEpochHints62
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CompilerCoordinateZero69
variable {F : Type} [Field F]
local instance fieldEquality : DecidableEq F := Classical.decEq F
def PairPrimitive (x y zx ix zy iy : F) : Prop :=
  CompilerZeroTest65.Primitive x zx ix ∧ CompilerZeroTest65.Primitive y zy iy
theorem complete (x y : F) : PairPrimitive x y
    (CompilerZeroTest65.indicator x) x⁻¹ (CompilerZeroTest65.indicator y) y⁻¹ :=
  ⟨CompilerZeroTest65.complete x,CompilerZeroTest65.complete y⟩
theorem pair_indicator (x y zx ix zy iy : F) (truth : PairPrimitive x y zx ix zy iy) :
    zx*zy=CompilerZeroTest65.indicator x*CompilerZeroTest65.indicator y := by
  rw [CompilerZeroTest65.indicator_sound x zx ix truth.1,
    CompilerZeroTest65.indicator_sound y zy iy truth.2]
theorem guard_iff (x y zx ix zy iy flag : F) (truth : PairPrimitive x y zx ix zy iy) :
    flag*(zx*zy)=0 ↔ (x=0 ∧ y=0 → flag=0) := by
  rw [pair_indicator x y zx ix zy iy truth]
  by_cases hx : x=0 <;> by_cases hy : y=0 <;>
    simp [CompilerZeroTest65.indicator,hx,hy]
theorem coordinate_guard_iff (x y a b zx ix zy iy flag : F)
    (truth : PairPrimitive (x-a) (y-b) zx ix zy iy) :
    flag*(zx*zy)=0 ↔ (x=a ∧ y=b → flag=0) := by
  simpa only [sub_eq_zero] using guard_iff (x-a) (y-b) zx ix zy iy flag truth
theorem canonical_pair_iff [CharP F CompilerArithmeticTransport41.p]
    (x y a b : Nat) (hx : x<CompilerArithmeticTransport41.p)
    (hy : y<CompilerArithmeticTransport41.p) (ha : a<CompilerArithmeticTransport41.p)
    (hb : b<CompilerArithmeticTransport41.p) :
    ((x:F)=(a:F) ∧ (y:F)=(b:F)) ↔ (x=a ∧ y=b) := by
  constructor
  · intro same
    exact ⟨CapturedEpochHints62.cast_small_unique x a hx ha same.1,
      CapturedEpochHints62.cast_small_unique y b hy hb same.2⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨rfl,rfl⟩
theorem canonical_guard_iff [CharP F CompilerArithmeticTransport41.p]
    (x y a b : Nat) (hx : x<CompilerArithmeticTransport41.p)
    (hy : y<CompilerArithmeticTransport41.p) (ha : a<CompilerArithmeticTransport41.p)
    (hb : b<CompilerArithmeticTransport41.p) (zx ix zy iy flag : F)
    (truth : PairPrimitive ((x:F)-(a:F)) ((y:F)-(b:F)) zx ix zy iy) :
    flag*(zx*zy)=0 ↔ (x=a ∧ y=b → flag=0) := by
  rw [coordinate_guard_iff (x:F) (y:F) (a:F) (b:F) zx ix zy iy flag truth,
    canonical_pair_iff x y a b hx hy ha hb]
end ShielddSecurity.CompilerCoordinateZero69
