import ShielddSecurity.HeaderRegisteredConstruction310
import ShielddSecurity.BalanceMapPoint701
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapCompletionFlags718
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 WordHints210 TransferSem

def booleanize (value : F) : F := if value=1 then 1 else 0

theorem zero_selected : 21193∈SharedWordWitness221.seedColumns :=
  SharedWordWitness221.boolean_coverage (21258,21193)
    (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _
        (by decide +kernel : (21258,21193)∈CapturedBooleanSlots208B0083.slots)))))))

theorem zero_windows : CapturedWordRoot213.words.all (fun entry =>
    decide (21193<entry.1.start ∨ entry.1.start+entry.1.width≤21193))=true := by decide +kernel

theorem zero_assignments_outside (numbers : Nat → Nat) :
    21193∉(SharedWordFlags220.assignments SharedWordWitness221.wordSlots numbers).map Prod.fst := by
  intro present
  obtain ⟨pair,known,equal⟩ := List.mem_map.mp present
  obtain ⟨slot,slotMember,pairMember⟩ := List.mem_flatMap.mp known
  obtain ⟨entry,entryMember,slotEqual⟩ := List.mem_map.mp slotMember
  subst slot
  have inColumns := (List.of_mem_zip pairMember).1
  have outside := of_decide_eq_true (List.all_eq_true.mp zero_windows entry entryMember)
  obtain ⟨offset,bound,atColumn⟩ := List.mem_range'.mp inColumns
  simp only [Nat.one_mul] at atColumn
  omega

theorem zero_seeded (base prepared : Nat → F) (numbers : Nat → Nat) :
    SharedWordWitness221.seeded base (LegalWordNormalization272.normalized numbers)
      (LegalAliasMeanings276.fallback numbers (ZeroHintWordFrame303.flags prepared)) 21193=
      booleanize (prepared 21193) := by
  unfold SharedWordWitness221.seeded
  rw [BooleanHints207.seeded_selected _ _ _ 21193 zero_selected]
  change BooleanHints207.bitValue (SharedWordFlags220.chosen _ _ 21193)=_
  rw [SharedWordFlags220.chosen_outside _ _ 21193 (zero_assignments_outside _),
    LegalAliasMeanings276.fallback_fixed _ _ 21193 (by decide)]
  simp only [BooleanHints207.bitValue,ZeroHintWordFrame303.flags,booleanize,decide_eq_true_eq]

theorem zero_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) :
    HeaderRegisteredConstruction310.completed original c w initial 21193=
      booleanize (RegisteredConstructorFrame309.prepared original c w 21193) := by
  unfold HeaderRegisteredConstruction310.completed SharedWordWitness221.completed
  rw [SharedRegisteredGeneral308.candidate_original _ 21193 (by decide) (by decide)]
  exact zero_seeded _ _ _

theorem choice_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) :
    HeaderRegisteredConstruction310.completed original c w initial 20935=
      ((representation.value (RegisteredConstructorFrame309.prepared original c w 20937)%2:Nat):F) := by
  unfold HeaderRegisteredConstruction310.completed SharedWordWitness221.completed
  rw [SharedRegisteredGeneral308.candidate_original _ 20935 (by decide) (by decide)]
  have h := LegalAliasMeanings276.seeded_meaning
    (CapturedFourSubgroupSeed89.seeded (RegisteredConstructorFrame309.prepared original c w) initial)
    (HeaderRegisteredConstruction310.numbers original c w)
    (ZeroHintWordFrame303.flags (RegisteredConstructorFrame309.prepared original c w)) 20935
    (Or.inr (Or.inr rfl))
  simpa only [LegalWordNormalization272.normalized,if_false,if_true,show ¬(20935=9059) by decide,
    show ¬(20935=10591) by decide] using h

theorem selected_parity (u : F) : (((BalanceMapRoots700.selectedRoot u).val%2:Nat):F)=
    if BalanceMapRoots700.choice u then 1 else 0 := by
  rw [BalanceMapRoots700.selected_parity]
  split <;> rfl

theorem zero_booleanize (u : F) : booleanize (BalanceMapPoint701.zero u)=BalanceMapPoint701.zero u := by
  unfold BalanceMapPoint701.zero
  split <;> simp [booleanize]
end ShielddSecurity.MapCompletionFlags718

set_option pp.all true in
#check @ShielddSecurity.MapCompletionFlags718.zero_selected
#print axioms ShielddSecurity.MapCompletionFlags718.zero_selected

set_option pp.all true in
#check @ShielddSecurity.MapCompletionFlags718.zero_windows
#print axioms ShielddSecurity.MapCompletionFlags718.zero_windows

set_option pp.all true in
#check @ShielddSecurity.MapCompletionFlags718.zero_assignments_outside
#print axioms ShielddSecurity.MapCompletionFlags718.zero_assignments_outside

set_option pp.all true in
#check @ShielddSecurity.MapCompletionFlags718.zero_seeded
#print axioms ShielddSecurity.MapCompletionFlags718.zero_seeded

set_option pp.all true in
#check @ShielddSecurity.MapCompletionFlags718.zero_completed
#print axioms ShielddSecurity.MapCompletionFlags718.zero_completed

set_option pp.all true in
#check @ShielddSecurity.MapCompletionFlags718.choice_completed
#print axioms ShielddSecurity.MapCompletionFlags718.choice_completed

set_option pp.all true in
#check @ShielddSecurity.MapCompletionFlags718.selected_parity
#print axioms ShielddSecurity.MapCompletionFlags718.selected_parity

set_option pp.all true in
#check @ShielddSecurity.MapCompletionFlags718.zero_booleanize
#print axioms ShielddSecurity.MapCompletionFlags718.zero_booleanize
