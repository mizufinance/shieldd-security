import ShielddSecurity.WordNaturalSeed297
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RegistryNaturalSeed298
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open TransferSem

def fixedColumns : List Nat := [11,12,13,14,15,21,22,23,24,30,31,32,33,34,35,36,42,43,135]

def scalar (leaf : AssetLeaf) : Nat → Nat
  | 11 => leaf.value
  | 12 => leaf.nextIndex
  | 13 => leaf.nextValue
  | 14 => leaf.detection.x
  | 15 => leaf.detection.y
  | 21 => leaf.dailyLimit
  | 22 => leaf.routePolicy
  | 23 => leaf.ring.x
  | 24 => leaf.ring.y
  | 30 => leaf.ringID
  | 31 => leaf.policyID
  | 32 => leaf.permission
  | 33 => leaf.resource
  | 34 => leaf.audit.epoch
  | 35 => leaf.audit.payload.x
  | 36 => leaf.audit.payload.y
  | 42 => leaf.audit.checking.x
  | 43 => leaf.audit.checking.y
  | 135 => leaf.position
  | _ => 0

/-- Partial independent registry input encoder. Other original inputs are
retained for the remaining Transfer components. -/
def seed (base : Nat → F) (leaf : AssetLeaf) (column : Nat) : F :=
  if column ∈ fixedColumns then (scalar leaf column : F)
  else if 136 ≤ column ∧ column < 184 then
    (leaf.siblings ⟨((column - 136) / 3) % 16, Nat.mod_lt _ (by decide)⟩
      ⟨(column - 136) % 3, Nat.mod_lt _ (by decide)⟩ : F)
  else base column

theorem seed_fixed (base : Nat → F) (leaf : AssetLeaf) (column : Nat)
    (fixed : column ∈ fixedColumns) :
    seed base leaf column = (scalar leaf column : F) := by
  simp only [seed, if_pos fixed]

theorem seed_siblings (base : Nat → F) (leaf : AssetLeaf) (level : Fin 16) (slot : Fin 3) :
    seed base leaf (136 + 3 * level.val + slot.val) = (leaf.siblings level slot : F) := by
  have hl := level.isLt
  have hs := slot.isLt
  have outside : 136 + 3 * level.val + slot.val ∉ fixedColumns := by
    simp [fixedColumns]
    omega
  have inside : 136 ≤ 136 + 3 * level.val + slot.val ∧
      136 + 3 * level.val + slot.val < 184 := by omega
  simp only [seed, if_neg outside, if_pos inside]
  have difference : 136 + 3 * level.val + slot.val - 136 = 3 * level.val + slot.val := by omega
  have division : (3 * level.val + slot.val) / 3 = level.val := by omega
  have remainder : (3 * level.val + slot.val) % 3 = slot.val := by omega
  apply congrArg (fun value : Nat => (value : F))
  apply congrArg₂ leaf.siblings
  · apply Fin.ext
    change ((136 + 3 * level.val + slot.val - 136) / 3) % 16 = level.val
    rw [difference, division, Nat.mod_eq_of_lt hl]
  · apply Fin.ext
    change (136 + 3 * level.val + slot.val - 136) % 3 = slot.val
    rw [difference, remainder]

theorem represented_nat (value : Nat) (bounded : value < TransferCore.fieldModulus) :
    representation.value (value : F) = value :=
  ZMod.val_natCast_of_lt bounded

theorem recover_seed (base : Nat → F) (leaf : AssetLeaf)
    (canonical : fieldsCanonical (registryFields leaf)) :
    RegistryRecovery194.recover representation (seed base leaf) = leaf := by
  have bound0 : leaf.value < TransferCore.fieldModulus :=
    canonical _ (by simp [registryFields, pointFields])
  have decoded0 : representation.value (seed base leaf 11) = leaf.value := by
    rw [seed_fixed base leaf 11 (by simp [fixedColumns])]
    exact represented_nat _ bound0
  have bound1 : leaf.nextIndex < TransferCore.fieldModulus :=
    canonical _ (by simp [registryFields, pointFields])
  have decoded1 : representation.value (seed base leaf 12) = leaf.nextIndex := by
    rw [seed_fixed base leaf 12 (by simp [fixedColumns])]
    exact represented_nat _ bound1
  have bound2 : leaf.nextValue < TransferCore.fieldModulus :=
    canonical _ (by simp [registryFields, pointFields])
  have decoded2 : representation.value (seed base leaf 13) = leaf.nextValue := by
    rw [seed_fixed base leaf 13 (by simp [fixedColumns])]
    exact represented_nat _ bound2
  have bound3 : leaf.detection.x < TransferCore.fieldModulus :=
    canonical _ (by simp [registryFields, pointFields])
  have decoded3 : representation.value (seed base leaf 14) = leaf.detection.x := by
    rw [seed_fixed base leaf 14 (by simp [fixedColumns])]
    exact represented_nat _ bound3
  have bound4 : leaf.detection.y < TransferCore.fieldModulus :=
    canonical _ (by simp [registryFields, pointFields])
  have decoded4 : representation.value (seed base leaf 15) = leaf.detection.y := by
    rw [seed_fixed base leaf 15 (by simp [fixedColumns])]
    exact represented_nat _ bound4
  have bound5 : leaf.dailyLimit < TransferCore.fieldModulus :=
    canonical _ (by simp [registryFields, pointFields])
  have decoded5 : representation.value (seed base leaf 21) = leaf.dailyLimit := by
    rw [seed_fixed base leaf 21 (by simp [fixedColumns])]
    exact represented_nat _ bound5
  have bound6 : leaf.routePolicy < TransferCore.fieldModulus :=
    canonical _ (by simp [registryFields, pointFields])
  have decoded6 : representation.value (seed base leaf 22) = leaf.routePolicy := by
    rw [seed_fixed base leaf 22 (by simp [fixedColumns])]
    exact represented_nat _ bound6
  have bound7 : leaf.ring.x < TransferCore.fieldModulus :=
    canonical _ (by simp [registryFields, pointFields])
  have decoded7 : representation.value (seed base leaf 23) = leaf.ring.x := by
    rw [seed_fixed base leaf 23 (by simp [fixedColumns])]
    exact represented_nat _ bound7
  have bound8 : leaf.ring.y < TransferCore.fieldModulus :=
    canonical _ (by simp [registryFields, pointFields])
  have decoded8 : representation.value (seed base leaf 24) = leaf.ring.y := by
    rw [seed_fixed base leaf 24 (by simp [fixedColumns])]
    exact represented_nat _ bound8
  have bound9 : leaf.ringID < TransferCore.fieldModulus :=
    canonical _ (by simp [registryFields, pointFields])
  have decoded9 : representation.value (seed base leaf 30) = leaf.ringID := by
    rw [seed_fixed base leaf 30 (by simp [fixedColumns])]
    exact represented_nat _ bound9
  have bound10 : leaf.policyID < TransferCore.fieldModulus :=
    canonical _ (by simp [registryFields, pointFields])
  have decoded10 : representation.value (seed base leaf 31) = leaf.policyID := by
    rw [seed_fixed base leaf 31 (by simp [fixedColumns])]
    exact represented_nat _ bound10
  have bound11 : leaf.permission < TransferCore.fieldModulus :=
    canonical _ (by simp [registryFields, pointFields])
  have decoded11 : representation.value (seed base leaf 32) = leaf.permission := by
    rw [seed_fixed base leaf 32 (by simp [fixedColumns])]
    exact represented_nat _ bound11
  have bound12 : leaf.resource < TransferCore.fieldModulus :=
    canonical _ (by simp [registryFields, pointFields])
  have decoded12 : representation.value (seed base leaf 33) = leaf.resource := by
    rw [seed_fixed base leaf 33 (by simp [fixedColumns])]
    exact represented_nat _ bound12
  have bound13 : leaf.audit.epoch < TransferCore.fieldModulus :=
    canonical _ (by simp [registryFields, pointFields])
  have decoded13 : representation.value (seed base leaf 34) = leaf.audit.epoch := by
    rw [seed_fixed base leaf 34 (by simp [fixedColumns])]
    exact represented_nat _ bound13
  have bound14 : leaf.audit.payload.x < TransferCore.fieldModulus :=
    canonical _ (by simp [registryFields, pointFields])
  have decoded14 : representation.value (seed base leaf 35) = leaf.audit.payload.x := by
    rw [seed_fixed base leaf 35 (by simp [fixedColumns])]
    exact represented_nat _ bound14
  have bound15 : leaf.audit.payload.y < TransferCore.fieldModulus :=
    canonical _ (by simp [registryFields, pointFields])
  have decoded15 : representation.value (seed base leaf 36) = leaf.audit.payload.y := by
    rw [seed_fixed base leaf 36 (by simp [fixedColumns])]
    exact represented_nat _ bound15
  have bound16 : leaf.audit.checking.x < TransferCore.fieldModulus :=
    canonical _ (by simp [registryFields, pointFields])
  have decoded16 : representation.value (seed base leaf 42) = leaf.audit.checking.x := by
    rw [seed_fixed base leaf 42 (by simp [fixedColumns])]
    exact represented_nat _ bound16
  have bound17 : leaf.audit.checking.y < TransferCore.fieldModulus :=
    canonical _ (by simp [registryFields, pointFields])
  have decoded17 : representation.value (seed base leaf 43) = leaf.audit.checking.y := by
    rw [seed_fixed base leaf 43 (by simp [fixedColumns])]
    exact represented_nat _ bound17
  have bound18 : leaf.position < TransferCore.fieldModulus :=
    canonical _ (by simp [registryFields, pointFields])
  have decoded18 : representation.value (seed base leaf 135) = leaf.position := by
    rw [seed_fixed base leaf 135 (by simp [fixedColumns])]
    exact represented_nat _ bound18
  have path : (fun (level : Fin 16) (slot : Fin 3) =>
      representation.value (seed base leaf (136 + 3 * level.val + slot.val))) = leaf.siblings := by
    funext level slot
    rw [seed_siblings]
    apply represented_nat
    apply canonical
    have member : leaf.siblings level slot ∈ pathFields leaf.siblings := by
      exact List.mem_flatMap.mpr ⟨level, by simp,
        List.mem_map.mpr ⟨slot, by simp, rfl⟩⟩
    exact List.mem_append_right _ member
  unfold RegistryRecovery194.recover
  simp only [decoded0, decoded1, decoded2, decoded3, decoded4, decoded5, decoded6, decoded7, decoded8, decoded9, decoded10, decoded11, decoded12, decoded13, decoded14, decoded15, decoded16, decoded17, decoded18, path]

theorem untouched (base : Nat → F) (leaf : AssetLeaf) (column : Nat)
    (outsideFixed : column ∉ fixedColumns)
    (outsidePath : ¬ (136 ≤ column ∧ column < 184)) :
    seed base leaf column = base column := by
  simp only [seed, if_neg outsideFixed, if_neg outsidePath]

theorem epoch_word_bound (c : Crypto) (w : TransferSem.Witness) (base : Nat → F)
    (canonical : fieldsCanonical (registryFields w.registry)) (legal : RegistrySem c w) :
    WordNaturalSeed297.numbers (seed base w.registry) 34 < 2 ^ 64 := by
  have recovered := recover_seed base w.registry canonical
  have epoch := congrArg (fun leaf : AssetLeaf => leaf.audit.epoch) recovered
  change representation.value (seed base w.registry 34) < 2 ^ 64
  change representation.value (seed base w.registry 34) = w.registry.audit.epoch at epoch
  rw [epoch]
  exact legal.2.2.2.2.1

theorem position_word_bound (c : Crypto) (w : TransferSem.Witness) (base : Nat → F)
    (canonical : fieldsCanonical (registryFields w.registry)) (legal : RegistrySem c w) :
    WordNaturalSeed297.numbers (seed base w.registry) 135 < 2 ^ 32 := by
  have recovered := recover_seed base w.registry canonical
  have position := congrArg (fun leaf : AssetLeaf => leaf.position) recovered
  change representation.value (seed base w.registry 135) < 2 ^ 32
  change representation.value (seed base w.registry 135) = w.registry.position at position
  rw [position]
  exact legal.2.2.2.2.2.1
end ShielddSecurity.RegistryNaturalSeed298


set_option pp.all true in
#check @ShielddSecurity.RegistryNaturalSeed298.fixedColumns
#print axioms ShielddSecurity.RegistryNaturalSeed298.fixedColumns

set_option pp.all true in
#check @ShielddSecurity.RegistryNaturalSeed298.scalar
#print axioms ShielddSecurity.RegistryNaturalSeed298.scalar

set_option pp.all true in
#check @ShielddSecurity.RegistryNaturalSeed298.seed
#print axioms ShielddSecurity.RegistryNaturalSeed298.seed

set_option pp.all true in
#check @ShielddSecurity.RegistryNaturalSeed298.seed_fixed
#print axioms ShielddSecurity.RegistryNaturalSeed298.seed_fixed

set_option pp.all true in
#check @ShielddSecurity.RegistryNaturalSeed298.seed_siblings
#print axioms ShielddSecurity.RegistryNaturalSeed298.seed_siblings

set_option pp.all true in
#check @ShielddSecurity.RegistryNaturalSeed298.represented_nat
#print axioms ShielddSecurity.RegistryNaturalSeed298.represented_nat

set_option pp.all true in
#check @ShielddSecurity.RegistryNaturalSeed298.recover_seed
#print axioms ShielddSecurity.RegistryNaturalSeed298.recover_seed

set_option pp.all true in
#check @ShielddSecurity.RegistryNaturalSeed298.untouched
#print axioms ShielddSecurity.RegistryNaturalSeed298.untouched

set_option pp.all true in
#check @ShielddSecurity.RegistryNaturalSeed298.epoch_word_bound
#print axioms ShielddSecurity.RegistryNaturalSeed298.epoch_word_bound

set_option pp.all true in
#check @ShielddSecurity.RegistryNaturalSeed298.position_word_bound
#print axioms ShielddSecurity.RegistryNaturalSeed298.position_word_bound
