import ShielddSecurity.UserSubgroupFrame354
import ShielddSecurity.UserSubgroupCapture355
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedUserSubgroups356
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def initial (senderInitial receiverInitial : Fin 3 → Group.Point F) (group : Fin 6) : Group.Point F :=
  if before : group.val<3 then senderInitial ⟨group.val,before⟩ else receiverInitial ⟨group.val-3,by omega⟩

theorem input_roles (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (registryInitial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (senderBinding : ∀ slot,CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) (senderInitial slot)=
      SubgroupSeedCompletion203.fieldPoint (UserPointDomain351.point w.sender slot))
    (receiverBinding : ∀ slot,CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) (receiverInitial slot)=
      SubgroupSeedCompletion203.fieldPoint (UserPointDomain351.point w.receiver slot)) :
    ∀ group,CapturedFourSubgroupConstructor88.InputRoles
      (fun column => UserLifecycleWord345.assignment (UserSubgroupSeed352.seed original w senderInitial receiverInitial) c w registryInitial
        (UserSubgroupCapture355.rename group column)) (initial senderInitial receiverInitial group) := by
  intro group
  rcases group with ⟨group,bound⟩
  have cases : group=0 ∨ group=1 ∨ group=2 ∨ group=3 ∨ group=4 ∨ group=5 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · refine ⟨?_,?_,?_,?_,?_⟩
    · exact (UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨0,by decide⟩ ⟨0,by decide⟩).trans (congrArg Group.Point.x (senderBinding ⟨0,by decide⟩)).symm
    · exact (UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨0,by decide⟩ ⟨1,by decide⟩).trans (congrArg Group.Point.y (senderBinding ⟨0,by decide⟩)).symm
    · exact UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨0,by decide⟩ ⟨2,by decide⟩
    · exact UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨0,by decide⟩ ⟨3,by decide⟩
    · intro index before
      have cases : index=0 ∨ index=1 ∨ index=2 := by omega
      rcases cases with rfl|rfl|rfl
      · exact UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨0,by decide⟩ ⟨4,by decide⟩
      · exact UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨0,by decide⟩ ⟨5,by decide⟩
      · exact UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨0,by decide⟩ ⟨6,by decide⟩
  · refine ⟨?_,?_,?_,?_,?_⟩
    · exact (UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨1,by decide⟩ ⟨0,by decide⟩).trans (congrArg Group.Point.x (senderBinding ⟨1,by decide⟩)).symm
    · exact (UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨1,by decide⟩ ⟨1,by decide⟩).trans (congrArg Group.Point.y (senderBinding ⟨1,by decide⟩)).symm
    · exact UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨1,by decide⟩ ⟨2,by decide⟩
    · exact UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨1,by decide⟩ ⟨3,by decide⟩
    · intro index before
      have cases : index=0 ∨ index=1 ∨ index=2 := by omega
      rcases cases with rfl|rfl|rfl
      · exact UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨1,by decide⟩ ⟨4,by decide⟩
      · exact UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨1,by decide⟩ ⟨5,by decide⟩
      · exact UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨1,by decide⟩ ⟨6,by decide⟩
  · refine ⟨?_,?_,?_,?_,?_⟩
    · exact (UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨2,by decide⟩ ⟨0,by decide⟩).trans (congrArg Group.Point.x (senderBinding ⟨2,by decide⟩)).symm
    · exact (UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨2,by decide⟩ ⟨1,by decide⟩).trans (congrArg Group.Point.y (senderBinding ⟨2,by decide⟩)).symm
    · exact UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨2,by decide⟩ ⟨2,by decide⟩
    · exact UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨2,by decide⟩ ⟨3,by decide⟩
    · intro index before
      have cases : index=0 ∨ index=1 ∨ index=2 := by omega
      rcases cases with rfl|rfl|rfl
      · exact UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨2,by decide⟩ ⟨4,by decide⟩
      · exact UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨2,by decide⟩ ⟨5,by decide⟩
      · exact UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨2,by decide⟩ ⟨6,by decide⟩
  · refine ⟨?_,?_,?_,?_,?_⟩
    · exact (UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨0,by decide⟩ ⟨0,by decide⟩).trans (congrArg Group.Point.x (receiverBinding ⟨0,by decide⟩)).symm
    · exact (UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨0,by decide⟩ ⟨1,by decide⟩).trans (congrArg Group.Point.y (receiverBinding ⟨0,by decide⟩)).symm
    · exact UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨0,by decide⟩ ⟨2,by decide⟩
    · exact UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨0,by decide⟩ ⟨3,by decide⟩
    · intro index before
      have cases : index=0 ∨ index=1 ∨ index=2 := by omega
      rcases cases with rfl|rfl|rfl
      · exact UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨0,by decide⟩ ⟨4,by decide⟩
      · exact UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨0,by decide⟩ ⟨5,by decide⟩
      · exact UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨0,by decide⟩ ⟨6,by decide⟩
  · refine ⟨?_,?_,?_,?_,?_⟩
    · exact (UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨1,by decide⟩ ⟨0,by decide⟩).trans (congrArg Group.Point.x (receiverBinding ⟨1,by decide⟩)).symm
    · exact (UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨1,by decide⟩ ⟨1,by decide⟩).trans (congrArg Group.Point.y (receiverBinding ⟨1,by decide⟩)).symm
    · exact UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨1,by decide⟩ ⟨2,by decide⟩
    · exact UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨1,by decide⟩ ⟨3,by decide⟩
    · intro index before
      have cases : index=0 ∨ index=1 ∨ index=2 := by omega
      rcases cases with rfl|rfl|rfl
      · exact UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨1,by decide⟩ ⟨4,by decide⟩
      · exact UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨1,by decide⟩ ⟨5,by decide⟩
      · exact UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨1,by decide⟩ ⟨6,by decide⟩
  · refine ⟨?_,?_,?_,?_,?_⟩
    · exact (UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨2,by decide⟩ ⟨0,by decide⟩).trans (congrArg Group.Point.x (receiverBinding ⟨2,by decide⟩)).symm
    · exact (UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨2,by decide⟩ ⟨1,by decide⟩).trans (congrArg Group.Point.y (receiverBinding ⟨2,by decide⟩)).symm
    · exact UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨2,by decide⟩ ⟨2,by decide⟩
    · exact UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨2,by decide⟩ ⟨3,by decide⟩
    · intro index before
      have cases : index=0 ∨ index=1 ∨ index=2 := by omega
      rcases cases with rfl|rfl|rfl
      · exact UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨2,by decide⟩ ⟨4,by decide⟩
      · exact UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨2,by decide⟩ ⟨5,by decide⟩
      · exact UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨2,by decide⟩ ⟨6,by decide⟩

theorem initial_valid (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (senderValid : ∀ slot,Group.OnCurve (CapturedFirstSubgroup81.d:F) (senderInitial slot))
    (receiverValid : ∀ slot,Group.OnCurve (CapturedFirstSubgroup81.d:F) (receiverInitial slot)) :
    ∀ group,Group.OnCurve (CapturedFirstSubgroup81.d:F) (initial senderInitial receiverInitial group) := by
  intro group
  unfold initial
  split
  · exact senderValid _
  · exact receiverValid _

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (registryInitial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (senderValid : ∀ slot,Group.OnCurve (CapturedFirstSubgroup81.d:F) (senderInitial slot))
    (receiverValid : ∀ slot,Group.OnCurve (CapturedFirstSubgroup81.d:F) (receiverInitial slot))
    (senderBinding : ∀ slot,CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) (senderInitial slot)=
      SubgroupSeedCompletion203.fieldPoint (UserPointDomain351.point w.sender slot))
    (receiverBinding : ∀ slot,CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) (receiverInitial slot)=
      SubgroupSeedCompletion203.fieldPoint (UserPointDomain351.point w.receiver slot)) :
    UserSubgroupCapture355.Rows
      (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed original w senderInitial receiverInitial) c w registryInitial) := by
  let base := UserSubgroupSeed352.seed original w senderInitial receiverInitial
  let rho := UserLifecycleWord345.assignment base c w registryInitial
  have zero := SharedHighZeroRows333.zero (UserWordSeed342.seed base w) c w registryInitial
  have linked := SharedComparisonBlocks327.linked (HighZeroSeed329.seed (UserWordSeed342.seed base w) w) c w registryInitial
  change rho 0=1 at zero
  change rho copy=rho 0 at linked
  exact UserSubgroupCapture355.complete rho (initial senderInitial receiverInitial) ConcreteJubjubField01.imaginary zero linked
    (SharedHighZeroRows333.arithmetic (UserWordSeed342.seed base w) c w registryInitial)
    (input_roles original c w registryInitial senderInitial receiverInitial senderBinding receiverBinding)
    (initial_valid senderInitial receiverInitial senderValid receiverValid)
    (by rw [coefficient_eq]; exact ConcreteJubjubField01.coefficient_no_unit_square) ConcreteJubjubField01.imaginary_square

theorem word_values_checked : CapturedWordRoot213.words.all (fun entry => decide
    (entry.1.width<255 → ¬ (1504≤entry.1.value ∧ entry.1.value<1528) ∧ ¬ (1742≤entry.1.value ∧ entry.1.value<1766))) = true := by decide +kernel

theorem word_values_outside (entry : WordHints210.Slot × Nat) (member : entry ∈ CapturedWordRoot213.words) (small : entry.1.width<255) :
    ¬ (1504≤entry.1.value ∧ entry.1.value<1528) ∧ ¬ (1742≤entry.1.value ∧ entry.1.value<1766) :=
  (of_decide_eq_true (List.all_eq_true.mp word_values_checked entry member)) small

theorem prepared_number_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (entry : WordHints210.Slot × Nat)
    (member : entry ∈ CapturedWordRoot213.words) (small : entry.1.width<255) :
    WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined (RegistryComparisonSeed318.seed
      (HighZeroSeed329.seed (UserWordSeed342.seed (UserSubgroupSeed352.seed original w senderInitial receiverInitial) w) w) w) c w) entry.1.value =
    WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined (RegistryComparisonSeed318.seed
      (HighZeroSeed329.seed (UserWordSeed342.seed original w) w) w) c w) entry.1.value := by
  have outside := word_values_outside entry member small
  unfold WordNaturalSeed297.numbers
  apply congrArg representation.value
  unfold HeaderRegistrySeed299.combined RegistryNaturalSeed298.seed HeaderRegistrySeed299.seed
    RegistryComparisonSeed318.seed HighZeroSeed329.seed FieldZeroSeed125.seeded UserWordSeed342.seed
  rw [UserSubgroupSeed352.outside original w senderInitial receiverInitial entry.1.value outside.1 outside.2]
end ShielddSecurity.SharedUserSubgroups356

set_option pp.all true in
#check @ShielddSecurity.SharedUserSubgroups356.initial
#print axioms ShielddSecurity.SharedUserSubgroups356.initial

set_option pp.all true in
#check @ShielddSecurity.SharedUserSubgroups356.input_roles
#print axioms ShielddSecurity.SharedUserSubgroups356.input_roles

set_option pp.all true in
#check @ShielddSecurity.SharedUserSubgroups356.initial_valid
#print axioms ShielddSecurity.SharedUserSubgroups356.initial_valid

set_option pp.all true in
#check @ShielddSecurity.SharedUserSubgroups356.all_rows
#print axioms ShielddSecurity.SharedUserSubgroups356.all_rows

set_option pp.all true in
#check @ShielddSecurity.SharedUserSubgroups356.word_values_checked
#print axioms ShielddSecurity.SharedUserSubgroups356.word_values_checked

set_option pp.all true in
#check @ShielddSecurity.SharedUserSubgroups356.word_values_outside
#print axioms ShielddSecurity.SharedUserSubgroups356.word_values_outside

set_option pp.all true in
#check @ShielddSecurity.SharedUserSubgroups356.prepared_number_frame
#print axioms ShielddSecurity.SharedUserSubgroups356.prepared_number_frame
