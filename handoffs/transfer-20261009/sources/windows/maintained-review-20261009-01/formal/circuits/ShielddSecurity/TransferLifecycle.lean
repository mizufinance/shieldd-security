import ShielddSecurity.TransferReduction
import ShielddSecurity.TransferAdmission
import ShielddSecurity.TreeBinding

set_option maxHeartbeats 300000

namespace ShielddSecurity.TransferLifecycle

variable {F : Type} [Field F] [CharP F Scalar.modulus]

/-- Active before freeze and active after unfreeze, with a strictly increased u64
generation retained and the frozen height reset. Native checked increment and
status/height updates must establish these particular packed values. -/
theorem active_generation_distinct (oldGeneration newGeneration : Nat)
    (increased : oldGeneration < newGeneration) (generationFits : newGeneration < 2 ^ 64) :
    ((1 + 8 * oldGeneration : Nat) : F) ≠ ((1 + 8 * newGeneration : Nat) : F) := by
  have oldBound : 1 + 8 * oldGeneration < Scalar.modulus := by
    simp only [Scalar.modulus] at ⊢
    omega
  have newBound : 1 + 8 * newGeneration < Scalar.modulus := by
    simp only [Scalar.modulus] at ⊢
    omega
  intro same
  have integer := bounded_cast_injective (F := F) (p := Scalar.modulus)
    oldBound newBound same
  omega

def RelevantCollision (leafHash treeHash : List F → F) : Prop :=
  (∃ left right, left.length = 9 ∧ right.length = 9 ∧
    left ≠ right ∧ leafHash left = leafHash right) ∨
  (∃ level left right, level < 16 ∧ left.length = 5 ∧ right.length = 5 ∧
    left ≠ right ∧ treeHash left = treeHash right)

def userRoot (leafHash treeHash : List F → F) (fields : List F)
    (path : List (TreeBinding.Step F)) : F :=
  TreeBinding.root (fun i children => treeHash (((i + 1 : Nat) : F) :: children))
    0 (leafHash fields) path

/-- Same-position roots after a generation change yield a concrete leaf or tree
collision. Hash interpretations, both eight-field leaf prefixes and actual
sixteen-level path alignment remain explicit application/source joins. -/
theorem equal_root_exposes_collision (leafHash treeHash : List F → F)
    (oldPrefix newPrefix : List F) (oldLength : oldPrefix.length = 8)
    (newLength : newPrefix.length = 8) (oldGeneration newGeneration : Nat)
    (increased : oldGeneration < newGeneration) (generationFits : newGeneration < 2 ^ 64)
    (oldPath newPath : List (TreeBinding.Step F))
    (aligned : TreeBinding.Aligned oldPath newPath) (height : oldPath.length = 16)
    (sameRoot : userRoot leafHash treeHash
      (oldPrefix ++ [((1 + 8 * oldGeneration : Nat) : F)]) oldPath =
      userRoot leafHash treeHash
      (newPrefix ++ [((1 + 8 * newGeneration : Nat) : F)]) newPath) :
    RelevantCollision leafHash treeHash := by
  let oldFields := oldPrefix ++ [((1 + 8 * oldGeneration : Nat) : F)]
  let newFields := newPrefix ++ [((1 + 8 * newGeneration : Nat) : F)]
  have distinct : oldFields ≠ newFields := by
    intro same
    have tail := List.append_singleton_inj.mp same
    exact active_generation_distinct oldGeneration newGeneration increased generationFits tail.2
  by_cases leafSame : leafHash oldFields = leafHash newFields
  · exact Or.inl ⟨oldFields, newFields, by simp [oldFields, oldLength],
      by simp [newFields, newLength], distinct, leafSame⟩
  · obtain ⟨level, left, right, lower, upper, leftLength, rightLength, different, equal⟩ :=
      TreeBinding.framed_root_collision treeHash 0 oldPath newPath aligned
        (leafHash oldFields) (leafHash newFields) leafSame sameRoot
    exact Or.inr ⟨level, left, right, by simpa [height] using upper,
      leftLength, rightLength, different, equal⟩

/-- If an old active snapshot is admitted after the successful freeze epoch
change, it took the current-pair branch and therefore exposes the same-position
hash collision. This derives the previously open noncurrent premise. -/
theorem admitted_old_snapshot_exposes_collision
    (codec : TransferReduction.CanonicalField F) (leafHash treeHash : List F → F)
    (oldPrefix newPrefix : List F) (oldLength : oldPrefix.length = 8)
    (newLength : newPrefix.length = 8) (oldGeneration newGeneration : Nat)
    (increased : oldGeneration < newGeneration) (generationFits : newGeneration < 2 ^ 64)
    (oldPath newPath : List (TreeBinding.Step F))
    (aligned : TreeBinding.Aligned oldPath newPath) (height : oldPath.length = 16)
    (current requested : TransferAdmission.Pair) (snapshot : TransferAdmission.Snapshot)
    (epoch now grace : Nat) (changed : snapshot.epoch ≠ epoch)
    (oldRole : requested.userRoot = codec.decode (userRoot leafHash treeHash
      (oldPrefix ++ [((1 + 8 * oldGeneration : Nat) : F)]) oldPath))
    (newRole : current.userRoot = codec.decode (userRoot leafHash treeHash
      (newPrefix ++ [((1 + 8 * newGeneration : Nat) : F)]) newPath))
    (admitted : TransferAdmission.PairAdmitted current requested (some snapshot) epoch now grace) :
    RelevantCollision leafHash treeHash := by
  by_cases samePair : requested = current
  · have sameDecoded := congrArg TransferAdmission.Pair.userRoot samePair
    rw [oldRole, newRole] at sameDecoded
    have sameRoot := congrArg (fun n : Nat => (n : F)) sameDecoded
    dsimp at sameRoot
    rw [codec.roundtrip, codec.roundtrip] at sameRoot
    exact equal_root_exposes_collision leafHash treeHash oldPrefix newPrefix oldLength newLength oldGeneration
      newGeneration increased generationFits oldPath newPath aligned height sameRoot
  · exact False.elim (TransferAdmission.epoch_change_does_not_revive_history
      current requested snapshot epoch now grace samePair changed admitted)

set_option pp.all true in
#check @active_generation_distinct
#print axioms active_generation_distinct
set_option pp.all true in
#check @equal_root_exposes_collision
#print axioms equal_root_exposes_collision
set_option pp.all true in
#check @admitted_old_snapshot_exposes_collision
#print axioms admitted_old_snapshot_exposes_collision

end ShielddSecurity.TransferLifecycle
