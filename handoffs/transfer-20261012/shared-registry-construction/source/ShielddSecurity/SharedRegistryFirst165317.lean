import ShielddSecurity.SharedRegulatedValue316
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedRegistryFirst165317
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open WordHints210 LegalWordNormalization272 TransferSem

theorem coverage_checked : (List.range 165).all (fun index => decide
    ((index = 0 ∨ (129 ≤ index ∧ index < 163)) →
      (CapturedBooleanSlots208B0000.slots.any (fun slot => decide (slot.1=index)) ||
       CapturedWordRoot213.words.any (fun entry => decide (entry.1.position=index))) = true)) = true := by decide +kernel

variable {K : Type} [Field K] [CharP K p]
theorem first165 (rho : Nat → K) (rows : LegalSharedRows271.Rows rho)
    (groups : ∀ group, Satisfies rho (CapturedFourSubgroupConstructor88.originalRows group))
    (anchor : ∃ row, CapturedFullRelation58.rowAt 178117 = some row ∧ Square (eval rho row.a) (eval rho row.b))
    (selectedRows : CompilerAssertionBlock51.SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (177979+index)) 104)
    (regulated : CompilerAssertionBlock51.SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (178118+index)) 1) :
    CompilerAssertionBlock51.SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (177954+index)) 165 := by
  intro index bound row found
  change CapturedFullRelation58.rowAt (177954+index) = some row at found
  by_cases group : 1 ≤ index ∧ index < 25
  · have offset : 177954+index=177955+(index-1) := by omega
    rw [offset] at found
    exact CapturedSubgroupPosition91.subgroup_positions rho groups (index-1) (by omega) row found
  by_cases inPrefix : 25 ≤ index ∧ index < 129
  · have offset : 177954+index=177979+(index-25) := by omega
    rw [offset] at found
    exact selectedRows (index-25) (by omega) row found
  by_cases last : index=164
  · subst index
    exact regulated 0 (by decide) row found
  by_cases anchored : index=163
  · subst index
    obtain ⟨selected,identity,square⟩ := anchor
    rw [found] at identity
    cases identity
    exact square
  have remaining : index=0 ∨ (129 ≤ index ∧ index<163) := by omega
  have check := of_decide_eq_true ((List.all_eq_true.mp coverage_checked) index (List.mem_range.mpr bound))
  rcases Bool.or_eq_true_iff.mp (check remaining) with boolean | word
  · obtain ⟨slot,member,position⟩ := List.any_eq_true.mp boolean
    have equal : slot.1=index := of_decide_eq_true position
    obtain ⟨selected,identity,square⟩ := rows.2.1 slot (SharedRegistryPrefix312.boolean_member slot member)
    rw [equal,found] at identity
    cases identity
    exact square
  · obtain ⟨entry,member,position⟩ := List.any_eq_true.mp word
    have equal : entry.1.position=index := of_decide_eq_true position
    obtain ⟨selected,identity,square⟩ := rows.2.2 entry member
    rw [equal,found] at identity
    cases identity
    exact square

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w)
    (remaining : ∀ entry ∈ CapturedWordRoot213.words, ¬ Alias entry.1.value →
      entry.1.width < 255 → entry.1.value ∉ HeaderSharedConstruction300.knownValues →
      WordNaturalSeed297.numbers (HeaderRegistrySeed299.combined original c w) entry.1.value < 2 ^ entry.1.width) :
    ∃ initial : Fin 4 → Group.Point F,
      LegalSharedRows271.Rows (HeaderRegisteredConstruction310.completed original c w initial) ∧
      CompilerAssertionBlock51.SatisfiesAt (HeaderRegisteredConstruction310.completed original c w initial)
        (fun index => CapturedFullRelation58.rowAt (177954+index)) 165 ∧
      representation.value (HeaderRegisteredConstruction310.completed original c w initial 1) =
        (crypto c).hash .transferStatement (publicFields (crypto c) w) ∧
      representation.value (HeaderRegisteredConstruction310.completed original c w initial 2) = w.blinding := by
  obtain ⟨initial,rows,groups,anchor,selectedRows,pub,committed⟩ := SharedRegistryPrefix312.legal_completed original c w legal remaining
  exact ⟨initial,rows,first165 _ rows groups anchor selectedRows
    (SharedRegulatedValue316.regulated_assertion original c w initial legal.2.1.1),pub,committed⟩
end ShielddSecurity.SharedRegistryFirst165317

set_option pp.all true in
#check @ShielddSecurity.SharedRegistryFirst165317.coverage_checked
#print axioms ShielddSecurity.SharedRegistryFirst165317.coverage_checked

set_option pp.all true in
#check @ShielddSecurity.SharedRegistryFirst165317.first165
#print axioms ShielddSecurity.SharedRegistryFirst165317.first165

set_option pp.all true in
#check @ShielddSecurity.SharedRegistryFirst165317.legal_completed
#print axioms ShielddSecurity.SharedRegistryFirst165317.legal_completed
