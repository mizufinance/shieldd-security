import ShielddSecurity.SharedEpochAssertions314
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedRegistryPrefix312
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open WordHints210 LegalWordNormalization272 TransferSem HeaderRegisteredConstruction310

theorem bits_checked : (List.range 64).all (fun index =>
    CapturedBooleanSlots208B0000.slots.any (fun slot => decide (slot.1 = 25 + index))) = true := by decide +kernel

theorem boolean_member (slot : Nat × Nat) (member : slot ∈ CapturedBooleanSlots208B0000.slots) :
    slot ∈ CapturedBooleanRoot209.slots :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ member))))

variable {K : Type} [Field K] [CharP K p]
theorem range_full (rho : Nat → K) (rows : LegalSharedRows271.Rows rho) :
    CompilerAssertionBlock51.SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (177979+index)) 65 := by
  intro index bound row found
  change CapturedFullRelation58.rowAt (177979+index) = some row at found
  by_cases bit : index < 64
  · have checked := (List.all_eq_true.mp bits_checked) index (List.mem_range.mpr bit)
    obtain ⟨slot,member,position⟩ := List.any_eq_true.mp checked
    have equal : slot.1 = 25+index := of_decide_eq_true position
    obtain ⟨selected,identity,square⟩ := rows.2.1 slot (boolean_member slot member)
    have offset : 177954+slot.1 = 177979+index := by omega
    rw [offset,found] at identity
    cases identity
    exact square
  · have last : index = 64 := by omega
    subst index
    obtain ⟨selected,identity,square⟩ := rows.2.2
      (CapturedWordSlots211B000.W00.slot,CapturedWordSlots211B000.W00.first)
      (List.mem_cons_self)
    change CapturedFullRelation58.rowAt 178043 = some selected at identity
    change CapturedFullRelation58.rowAt 178043 = some row at found
    rw [found] at identity
    cases identity
    exact square

theorem range_local (rho : Nat → K) (rows : LegalSharedRows271.Rows rho) :
    CompilerAssertionBlock51.SatisfiesAt rho CapturedEpochRange60.block.actual 65 := by
  have checks := Bool.and_eq_true_iff.mp CapturedGlobalEpoch64.range_checked
  have selected := (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt 177979 65
    CapturedGlobalEpoch64.rangeRows checks.1 rho).mpr (range_full rho rows)
  have localRows := (CompilerRowSlice63.selected_satisfies_iff CapturedEpochRange60.block.actual 0 65
    CapturedGlobalEpoch64.rangeRows checks.2 rho).mp selected
  simpa only [Nat.zero_add] using localRows
theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w)
    (remaining : ∀ entry ∈ CapturedWordRoot213.words, ¬ Alias entry.1.value →
      entry.1.width < 255 → entry.1.value ∉ HeaderSharedConstruction300.knownValues →
      WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined original c w) entry.1.value < 2 ^ entry.1.width) :
    ∃ initial : Fin 4 → Group.Point F,
      LegalSharedRows271.Rows (HeaderRegisteredConstruction310.completed original c w initial) ∧
      (∀ group, Satisfies (HeaderRegisteredConstruction310.completed original c w initial)
        (CapturedFourSubgroupConstructor88.originalRows group)) ∧
      (∃ row, CapturedFullRelation58.rowAt 178117 = some row ∧
        Square (eval (HeaderRegisteredConstruction310.completed original c w initial) row.a)
          (eval (HeaderRegisteredConstruction310.completed original c w initial) row.b)) ∧
      CompilerAssertionBlock51.SatisfiesAt (HeaderRegisteredConstruction310.completed original c w initial)
        (fun index => CapturedFullRelation58.rowAt (177979+index)) 104 ∧
      representation.value (HeaderRegisteredConstruction310.completed original c w initial 1) =
        (crypto c).hash .transferStatement (publicFields (crypto c) w) ∧
      representation.value (HeaderRegisteredConstruction310.completed original c w initial 2) = w.blinding := by
  obtain ⟨initial,rows,groups,anchor,registered,pub,committed⟩ :=
    HeaderRegisteredConstruction310.legal_completed original c w legal remaining
  exact ⟨initial,rows,groups,anchor,
    CapturedGlobalRegistered74.selected_global104 _ (range_local _ rows)
      (SharedEpochAssertions314.completed_assertions original c w initial legal.2.1.1) registered,pub,committed⟩
end ShielddSecurity.SharedRegistryPrefix312

set_option pp.all true in
#check @ShielddSecurity.SharedRegistryPrefix312.bits_checked
#print axioms ShielddSecurity.SharedRegistryPrefix312.bits_checked

set_option pp.all true in
#check @ShielddSecurity.SharedRegistryPrefix312.boolean_member
#print axioms ShielddSecurity.SharedRegistryPrefix312.boolean_member

set_option pp.all true in
#check @ShielddSecurity.SharedRegistryPrefix312.range_full
#print axioms ShielddSecurity.SharedRegistryPrefix312.range_full

set_option pp.all true in
#check @ShielddSecurity.SharedRegistryPrefix312.range_local
#print axioms ShielddSecurity.SharedRegistryPrefix312.range_local

set_option pp.all true in
#check @ShielddSecurity.SharedRegistryPrefix312.legal_completed
#print axioms ShielddSecurity.SharedRegistryPrefix312.legal_completed
