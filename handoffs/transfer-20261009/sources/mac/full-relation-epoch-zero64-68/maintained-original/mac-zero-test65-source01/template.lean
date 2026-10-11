import ShielddSecurity.CompilerAssertionBlock51
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CompilerZeroTest65
open CompilerAssertionBlock51
variable {F : Type} [Field F]
local instance fieldEquality : DecidableEq F := Classical.decEq F
def indicator (value : F) : F := if value=0 then 1 else 0
def Primitive (value zero inverse : F) : Prop :=
  Square zero zero ∧ value*inverse=1-zero ∧ value*zero=0
theorem complete (value : F) : Primitive value (indicator value) value⁻¹ := by
  by_cases isZero : value=0
  · simp [Primitive,indicator,isZero,Square]
  · simp [Primitive,indicator,isZero,Square]
theorem indicator_sound (value zero inverse : F) (truth : Primitive value zero inverse) :
    zero=indicator value := by
  by_cases isZero : value=0
  · have equation:=truth.2.1
    rw [isZero,zero_mul] at equation
    simpa only [indicator,if_pos isZero] using (sub_eq_zero.mp equation.symm).symm
  · have same:= (mul_eq_zero.mp truth.2.2).resolve_left isZero
    simpa only [indicator,if_neg isZero] using same
theorem zero_iff (value zero inverse : F) (truth : Primitive value zero inverse) :
    value=0 ↔ zero=1 := by
  constructor
  · intro isZero
    simpa only [indicator,isZero,if_true] using indicator_sound value zero inverse truth
  · intro isOne
    have equation:=truth.2.2
    simpa only [isOne,mul_one] using equation
theorem nonzero_iff (value zero inverse : F) (truth : Primitive value zero inverse) :
    value≠0 ↔ zero=0 := by
  constructor
  · intro notZero
    simpa only [indicator,if_neg notZero] using indicator_sound value zero inverse truth
  · intro isZero isValueZero
    have isOne:=(zero_iff value zero inverse truth).mp isValueZero
    exact zero_ne_one (isZero.symm.trans isOne)
theorem guard_iff (value zero inverse flag : F) (truth : Primitive value zero inverse) :
    flag*zero=0 ↔ (value=0 → flag=0) := by
  rw [indicator_sound value zero inverse truth]
  by_cases isZero : value=0
  · simp [indicator,isZero]
  · simp [indicator,isZero]
theorem equality_iff (left right zero inverse : F)
    (truth : Primitive (left-right) zero inverse) : left=right ↔ zero=1 := by
  rw [←sub_eq_zero,zero_iff (left-right) zero inverse truth]
end ShielddSecurity.CompilerZeroTest65
