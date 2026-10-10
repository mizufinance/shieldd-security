import ShielddSecurity.ConcreteEightTorsionData01

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcreteEightTorsionWitness01
open TorsionCertifiedField01 ConcretePointTorsion01 ConcreteEightTorsionData01

def point1 : curve.Point := WeierstrassCurve.Affine.Point.mk equation1
def point2 : curve.Point := WeierstrassCurve.Affine.Point.mk equation2
def point3 : curve.Point := WeierstrassCurve.Affine.Point.mk equation3

theorem double_one : 2 • point1 = point2 := by
  obtain ⟨output, doubled⟩ := ConcretePointCoordinateRows01.tangent_rows equation1
    double1_nonzero double1_slope double1_x double1_y
  rw [two_nsmul]
  exact doubled

theorem double_two : 2 • point2 = torsion := by
  obtain ⟨output, doubled⟩ := ConcretePointCoordinateRows01.tangent_rows equation2
    double2_nonzero double2_slope double2_x double2_y
  rw [two_nsmul]
  exact doubled

theorem triple_one : 3 • point1 = point3 := by
  obtain ⟨output, added⟩ := ConcretePointCoordinateRows01.secant_rows equation1 equation2
    add13_different add13_slope add13_x add13_y
  calc
    3 • point1 = point1 + 2 • point1 := by
      rw [show (3 : Nat) = 1 + 2 by rfl, add_nsmul, one_nsmul]
    _ = point3 := by rw [double_one]; exact added

theorem four_origin : 4 • point1 = torsion := by
  calc
    4 • point1 = 2 • (2 • point1) := by rw [← mul_nsmul]; rfl
    _ = torsion := by rw [double_one, double_two]

theorem eight_killed : 8 • point1 = 0 := by
  calc
    8 • point1 = 2 • (4 • point1) := by rw [← mul_nsmul]; rfl
    _ = 0 := by rw [four_origin, torsion_doubled]

theorem exact_order_eight : addOrderOf point1 = 8 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have fourNonzero : 4 • point1 ≠ 0 := by rw [four_origin]; exact torsion_nonzero
  have order := addOrderOf_eq_prime_pow (p := 2) (n := 2) fourNonzero eight_killed
  exact order

def kernelEight := (DoublingKernelBound01.multiply (J := curve.Point) 8).ker

noncomputable def enumerate (k : Fin 8) : kernelEight :=
  ⟨k.val • point1, by
    change 8 • (k.val • point1) = 0
    calc
      8 • (k.val • point1) = k.val • (8 • point1) := by
        rw [← mul_nsmul, ← mul_nsmul, Nat.mul_comm]
      _ = 0 := by rw [eight_killed, nsmul_zero]⟩

theorem enumerate_injective : Function.Injective enumerate := by
  intro left right equal
  have values := congrArg Subtype.val equal
  have residues := nsmul_inj_mod.mp values
  rw [exact_order_eight, Nat.mod_eq_of_lt left.isLt, Nat.mod_eq_of_lt right.isLt] at residues
  exact Fin.ext residues

theorem enumerate_surjective : Function.Surjective enumerate := by
  apply (enumerate_injective.bijective_of_nat_card_le ?_).2
  rw [Nat.card_fin]
  exact eight_kernel_bound

theorem kernel_cardinality : Nat.card kernelEight = 8 := by
  have lower := Nat.card_le_card_of_injective enumerate enumerate_injective
  rw [Nat.card_fin] at lower
  exact Nat.le_antisymm eight_kernel_bound lower

theorem eight_torsion_exhaustive (point : curve.Point) (killed : 8 • point = 0) :
    ∃ k : Fin 8, k.val • point1 = point := by
  obtain ⟨k, equal⟩ := enumerate_surjective ⟨point, killed⟩
  exact ⟨k, congrArg Subtype.val equal⟩

end ShielddSecurity.ConcreteEightTorsionWitness01

set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionWitness01.double_one
#print axioms ShielddSecurity.ConcreteEightTorsionWitness01.double_one
set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionWitness01.double_two
#print axioms ShielddSecurity.ConcreteEightTorsionWitness01.double_two
set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionWitness01.triple_one
#print axioms ShielddSecurity.ConcreteEightTorsionWitness01.triple_one
set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionWitness01.four_origin
#print axioms ShielddSecurity.ConcreteEightTorsionWitness01.four_origin
set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionWitness01.eight_killed
#print axioms ShielddSecurity.ConcreteEightTorsionWitness01.eight_killed
set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionWitness01.exact_order_eight
#print axioms ShielddSecurity.ConcreteEightTorsionWitness01.exact_order_eight
set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionWitness01.enumerate
#print axioms ShielddSecurity.ConcreteEightTorsionWitness01.enumerate
set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionWitness01.enumerate_injective
#print axioms ShielddSecurity.ConcreteEightTorsionWitness01.enumerate_injective
set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionWitness01.enumerate_surjective
#print axioms ShielddSecurity.ConcreteEightTorsionWitness01.enumerate_surjective
set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionWitness01.kernel_cardinality
#print axioms ShielddSecurity.ConcreteEightTorsionWitness01.kernel_cardinality
set_option pp.all true in
#check @ShielddSecurity.ConcreteEightTorsionWitness01.eight_torsion_exhaustive
#print axioms ShielddSecurity.ConcreteEightTorsionWitness01.eight_torsion_exhaustive
