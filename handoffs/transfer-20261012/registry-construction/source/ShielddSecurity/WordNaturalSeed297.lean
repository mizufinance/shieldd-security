import ShielddSecurity.ConcreteRegistrySharedEncoding294
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.WordNaturalSeed297
open ConcreteJubjubField01 ConcretePointTorsion01
open ConcreteRegistrySharedEncoding294 PoseidonNatural192 WordHints210 LegalWordNormalization272

/-- Every original field column is interpreted by its canonical integer.
This is an interpretation of a supplied field seed; it does not construct the
independently legal Transfer seed or derive its smaller semantic bounds. -/
def numbers (base : Nat → F) : Nat → Nat := fun column => representation.value (base column)

theorem number_cast (base : Nat → F) (column : Nat) :
    (numbers base column : F) = base column :=
  representation.cast_value _

theorem field_below_255 : TransferCore.fieldModulus < 2 ^ 255 := by decide +kernel

theorem number_below_255 (base : Nat → F) (column : Nat) :
    numbers base column < 2 ^ 255 :=
  lt_trans (representation.bounded _) field_below_255

theorem original_meanings (base : Nat → F) :
    ∀ entry ∈ CapturedWordRoot213.words, ¬ Alias entry.1.value →
      base entry.1.value = (numbers base entry.1.value : F) := by
  intro entry _ _
  exact (number_cast base entry.1.value).symm

theorem widths_checked : CapturedWordRoot213.words.all
    (fun entry => decide (entry.1.width ≤ 255)) = true := by decide +kernel

theorem all_widths (entry : Slot × Nat) (member : entry ∈ CapturedWordRoot213.words) :
    entry.1.width ≤ 255 :=
  of_decide_eq_true ((List.all_eq_true.mp widths_checked) entry member)

theorem all_bounds (base : Nat → F)
    (smaller : ∀ entry ∈ CapturedWordRoot213.words, ¬ Alias entry.1.value →
      entry.1.width < 255 → numbers base entry.1.value < 2 ^ entry.1.width) :
    ∀ entry ∈ CapturedWordRoot213.words, ¬ Alias entry.1.value →
      numbers base entry.1.value < 2 ^ entry.1.width := by
  intro entry member outside
  by_cases small : entry.1.width < 255
  · exact smaller entry member outside small
  · have equal : entry.1.width = 255 := by
      have bounded := all_widths entry member
      omega
    rw [equal]
    exact number_below_255 base entry.1.value

def Constructed (base : Nat → F) (old : Nat → Bool) : Prop :=
    ∃ initial : Fin 4 → Group.Point F,
      LegalSharedRows271.Rows (SharedWordWitness221.completed
        (CapturedFourSubgroupSeed89.seeded base initial) (normalized (numbers base))
        (LegalAliasMeanings276.fallback (numbers base) old)) ∧
      (∀ group, Satisfies (SharedWordWitness221.completed
        (CapturedFourSubgroupSeed89.seeded base initial) (normalized (numbers base))
        (LegalAliasMeanings276.fallback (numbers base) old))
        (CapturedFourSubgroupConstructor88.originalRows group)) ∧
      ∃ row, CapturedFullRelation58.rowAt 178117 = some row ∧
        Square
          (eval (SharedWordWitness221.completed
            (CapturedFourSubgroupSeed89.seeded base initial) (normalized (numbers base))
            (LegalAliasMeanings276.fallback (numbers base) old)) row.a)
          (eval (SharedWordWitness221.completed
            (CapturedFourSubgroupSeed89.seeded base initial) (normalized (numbers base))
            (LegalAliasMeanings276.fallback (numbers base) old)) row.b)

theorem legal_completed (c : TransferSem.Crypto) (base : Nat → F) (old : Nat → Bool)
    (one : base 0 = 1)
    (smaller : ∀ entry ∈ CapturedWordRoot213.words, ¬ Alias entry.1.value →
      entry.1.width < 255 → numbers base entry.1.value < 2 ^ entry.1.width)
    (w : TransferSem.Witness) (legal : TransferSem.RegistrySem (crypto c) w)
    (registry : RegistryRecovery194.recover representation base = w.registry)
    (anchor : representation.value (base 4) = w.assetAnchor) : Constructed base old :=
  ConcreteRegistrySharedEncoding294.legal_completed c base (numbers base) old one
    (all_bounds base smaller) (original_meanings base) rfl w legal registry anchor
end ShielddSecurity.WordNaturalSeed297

