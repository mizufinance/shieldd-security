import ShielddSecurity.TransferRegistryUserCompletion

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferUserLifecycleDecomposition

open TransferCore TransferSem TransferRegistryUserCompletion

/-! Recover the raw freeze-generation input from every legal active lifecycle.
This proves coverage of the lifecycle representation used by constructUser.
It does not authenticate a tree path, establish row/source correspondence or
construct a complete Transfer assignment. -/

private theorem generation_from_decomposition (lifecycle generation : Nat)
    (bounded : lifecycle < 2 ^ 67) (decomposition : 1 + 8 * generation = lifecycle) :
    generation < 2 ^ 64 := by
  change lifecycle < 147573952589676412928 at bounded
  change generation < 18446744073709551616
  omega

theorem active_lifecycle_decomposition (lifecycle : Nat)
    (active : lifecycle % 8 = 1) (highZero : lifecycle / 2 ^ 67 = 0) :
    lifecycle / 8 < 2 ^ 64 ∧ 1 + 8 * (lifecycle / 8) = lifecycle := by
  have division := Nat.mod_add_div lifecycle (2 ^ 67)
  rw [highZero, Nat.mul_zero, Nat.add_zero] at division
  have bound : lifecycle < 2 ^ 67 := division ▸ Nat.mod_lt lifecycle (by decide : 0 < 2 ^ 67)
  have reconstructed : 1 + 8 * (lifecycle / 8) = lifecycle := by
    simpa only [active] using Nat.mod_add_div lifecycle 8
  exact ⟨generation_from_decomposition lifecycle (lifecycle / 8) bound reconstructed, reconstructed⟩

def recoverPath (user : User) : UserPathInputs :=
  { freezeGeneration := user.lifecycle / 8
    inactiveLifecycle := user.lifecycle
    position := user.position
    siblings := user.siblings }

theorem reconstruct_user (regulated : Bool) (user : User)
    (legalActive : regulated = true → user.lifecycle % 8 = 1 ∧
      user.lifecycle / 2 ^ 67 = 0) :
    constructUser regulated user (recoverPath user) = user := by
  cases selected : regulated with
  | false =>
      cases user
      rfl
  | true =>
      have decomposed := active_lifecycle_decomposition user.lifecycle
        (legalActive selected).1 (legalActive selected).2
      simp only [constructUser, recoverPath, ↓reduceIte]
      rw [decomposed.2]

theorem user_sem_recovers_generation_and_record (c : Crypto)
    (w : TransferSem.Witness) (user : User) (legal : UserSem c w user) :
    (w.regulated = true → (recoverPath user).freezeGeneration < 2 ^ 64) ∧
    constructUser w.regulated user (recoverPath user) = user := by
  have active : w.regulated = true → user.lifecycle % 8 = 1 ∧
      user.lifecycle / 2 ^ 67 = 0 := by
    intro enabled
    have branch := legal.2.2.2.2.2.2.2.2 enabled
    exact ⟨branch.1, branch.2.1⟩
  refine ⟨?_, reconstruct_user w.regulated user active⟩
  intro enabled
  exact (active_lifecycle_decomposition user.lifecycle
    (active enabled).1 (active enabled).2).1

def recoverLegalPath (regulated : Bool) (user : User) : UserPathInputs :=
  { freezeGeneration := if regulated then user.lifecycle / 8 else 0
    inactiveLifecycle := user.lifecycle
    position := user.position
    siblings := user.siblings }

theorem legal_path_reconstructs_user (regulated : Bool) (user : User)
    (legalActive : regulated = true → user.lifecycle % 8 = 1 ∧ user.lifecycle / 2 ^ 67 = 0) :
    constructUser regulated user (recoverLegalPath regulated user) = user := by
  cases selected : regulated with
  | false =>
      cases user
      rfl
  | true =>
      exact reconstruct_user true user (fun _ => legalActive selected)

theorem user_sem_has_legal_raw_path (c : Crypto) (w : TransferSem.Witness) (user : User)
    (legal : UserSem c w user) (canonical : fieldsCanonical (userFields user)) :
    LegalUserPath c w user (recoverLegalPath w.regulated user) ∧
      constructUser w.regulated user (recoverLegalPath w.regulated user) = user := by
  have active : w.regulated = true → user.lifecycle % 8 = 1 ∧ user.lifecycle / 2 ^ 67 = 0 := by
    intro enabled
    have branch := legal.2.2.2.2.2.2.2.2 enabled
    exact ⟨branch.1, branch.2.1⟩
  have restored := legal_path_reconstructs_user w.regulated user active
  have pathCanonical : fieldsCanonical (pathFields user.siblings) := by
    simp only [userFields, TransferRegistryUserCompletion.fieldsCanonical_append] at canonical
    exact canonical.2
  refine ⟨⟨legal.1, legal.2.1, legal.2.2.1, legal.2.2.2.1, legal.2.2.2.2.1,
    legal.2.2.2.2.2.1, ?_, legal.2.2.2.2.2.2.1, legal.2.2.2.2.2.2.2.1,
    pathCanonical, ?_⟩, restored⟩
  · cases selected : w.regulated with
    | false => exact (by decide : (0 : Nat) < 2 ^ 64)
    | true => exact (active_lifecycle_decomposition user.lifecycle
        (active selected).1 (active selected).2).1
  · intro enabled
    simpa only [restored] using (legal.2.2.2.2.2.2.2.2 enabled).2.2

set_option pp.all true in
#check @active_lifecycle_decomposition
#print axioms active_lifecycle_decomposition
set_option pp.all true in
#check @reconstruct_user
#print axioms reconstruct_user
set_option pp.all true in
#check @user_sem_recovers_generation_and_record
#print axioms user_sem_recovers_generation_and_record
set_option pp.all true in
#check @legal_path_reconstructs_user
#print axioms legal_path_reconstructs_user
set_option pp.all true in
#check @user_sem_has_legal_raw_path
#print axioms user_sem_has_legal_raw_path

end ShielddSecurity.TransferUserLifecycleDecomposition
