import ShielddSecurity.CompletedComparisonValues323
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.ComparisonBorrowFrame324
open Compiler CompilerArithmeticTransport41 WordHints210

def borrowColumns : List Nat := [981,1112,1242,1373]

theorem windows_checked : CapturedWordRoot213.words.all (fun entry => borrowColumns.all (fun column =>
    decide (column < entry.1.start ∨ entry.1.start+entry.1.width ≤ column))) = true := by decide +kernel

theorem outside_assignments (numbers : Nat → Nat) (column : Nat) (selected : column ∈ borrowColumns) :
    column ∉ (SharedWordFlags220.assignments SharedWordWitness221.wordSlots numbers).map Prod.fst := by
  intro member
  obtain ⟨pair,known,equal⟩ := List.mem_map.mp member
  obtain ⟨slot,slotMember,pairMember⟩ := List.mem_flatMap.mp known
  obtain ⟨entry,entryMember,slotEqual⟩ := List.mem_map.mp slotMember
  subst slot
  have inside := (List.of_mem_zip pairMember).1
  have separation := of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp windows_checked) entry entryMember)) column selected)
  rcases pair with ⟨field,bit⟩
  change field=column at equal
  rw [equal] at inside
  obtain ⟨offset,before,same⟩ := List.mem_range'.mp inside
  simp only [Nat.one_mul] at same
  rcases separation with earlier | later <;> omega

variable {K : Type} [Field K] [CharP K p] [DecidableEq K]
theorem flag_frame (base : Nat → K) (numbers : Nat → Nat) (fallback : Nat → Bool)
    (column : Nat) (selected : column ∈ borrowColumns)
    (boolean : base column=0 ∨ base column=1)
    (meaning : fallback column=ZeroHintWordFrame303.flags base column) :
    SharedWordWitness221.completed base numbers fallback column=base column := by
  have bounds : 3 ≤ column ∧ column < 22738 := by
    simp only [borrowColumns,List.mem_cons,List.not_mem_nil,or_false] at selected
    rcases selected with first | second | third | fourth <;> omega
  change CapturedFullRelation58.candidate (SharedWordWitness221.seeded base numbers fallback) column = base column
  rw [SharedRegisteredGeneral308.candidate_original _ column bounds.1 bounds.2]
  by_cases seeded : column ∈ SharedWordWitness221.seedColumns
  · change BooleanHints207.seeded base _ _ column=base column
    rw [BooleanHints207.seeded_selected _ _ _ column seeded]
    change BooleanHints207.bitValue (SharedWordFlags220.chosen _ fallback column)=base column
    rw [SharedWordFlags220.chosen_outside _ fallback column (outside_assignments numbers column selected),meaning]
    exact ZeroHintWordFrame303.flags_cast base column boolean
  · exact BooleanHints207.seeded_outside base _ _ column seeded
end ShielddSecurity.ComparisonBorrowFrame324
namespace ShielddSecurity.ComparisonBorrowFrame324
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open WordHints210 LegalWordNormalization272 TransferSem RegisteredConstructorFrame309 HeaderRegisteredConstruction310

def value (w : TransferSem.Witness) (column : Nat) : F :=
  if column=981 then BinaryComparison100.bit (BoundedLimbComparison119.borrow (RegistryComparisonSeed318.high w.asset) (RegistryComparisonSeed318.high w.registry.value))
  else if column=1112 then BinaryComparison100.bit (BoundedLimbComparison119.borrow (RegistryComparisonSeed318.low w.asset) (RegistryComparisonSeed318.low w.registry.value))
  else if column=1242 then BinaryComparison100.bit (BoundedLimbComparison119.borrow (RegistryComparisonSeed318.high w.registry.nextValue) (RegistryComparisonSeed318.high w.asset))
  else if column=1373 then BinaryComparison100.bit (BoundedLimbComparison119.borrow (RegistryComparisonSeed318.low w.registry.nextValue) (RegistryComparisonSeed318.low w.asset))
  else 0

theorem seed_value (original : Nat → F) (w : TransferSem.Witness) (column : Nat) (selected : column ∈ borrowColumns) :
    RegistryComparisonSeed318.seed original w column=value w column := by
  simp only [borrowColumns,List.mem_cons,List.not_mem_nil,or_false] at selected
  rcases selected with rfl | rfl | rfl | rfl <;> simp [RegistryComparisonSeed318.seed,RegistryComparisonSeed318.comparisonValues,value]

theorem value_boolean (w : TransferSem.Witness) (column : Nat) : value w column=0 ∨ value w column=1 := by
  unfold value
  split_ifs <;> first
    | unfold BinaryComparison100.bit; split <;> simp
    | exact Or.inl rfl

theorem prepared_value (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (column : Nat) (selected : column ∈ borrowColumns) :
    prepared (RegistryComparisonSeed318.seed original w) c w column=value w column := by
  have ranges : 184 ≤ column ∧ column < 22737 := by
    simp only [borrowColumns,List.mem_cons,List.not_mem_nil,or_false] at selected
    rcases selected with first | second | third | fourth <;> omega
  have fixed : column ∉ RegistryNaturalSeed298.fixedColumns := by
    simp only [RegistryNaturalSeed298.fixedColumns,List.mem_cons,List.not_mem_nil,or_false]
    omega
  exact (prepared_outside (RegistryComparisonSeed318.seed original w) c w column (by omega)
    (by constructor <;> norm_num [copy] <;> omega)).trans
    ((RegistryNaturalSeed298.untouched _ w.registry column fixed (by omega)).trans
      ((HeaderRegistrySeed299.seed_outside _ c w column (by omega) (by omega)).trans
        (seed_value original w column selected)))

theorem completed_value (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (column : Nat) (selected : column ∈ borrowColumns) :
    HeaderRegisteredConstruction310.completed (RegistryComparisonSeed318.seed original w) c w initial column=value w column := by
  have outside : column ∉ CapturedFourSubgroupSeed89.hintColumns := by
    have lower : 981 ≤ column := by
      simp only [borrowColumns,List.mem_cons,List.not_mem_nil,or_false] at selected
      rcases selected with first | second | third | fourth <;> omega
    simp only [CapturedFourSubgroupSeed89.hintColumns,List.mem_cons,List.not_mem_nil,or_false]
    omega
  have group := CapturedFourSubgroupSeed89.seeded_outside
    (prepared (RegistryComparisonSeed318.seed original w) c w) initial column outside
  have flagValue := prepared_value original c w column selected
  have aliasOutside : ¬Alias column := by
    simp only [borrowColumns,List.mem_cons,List.not_mem_nil,or_false] at selected
    rcases selected with first | second | third | fourth <;> simp only [Alias] <;> omega
  have frame := flag_frame
    (CapturedFourSubgroupSeed89.seeded (prepared (RegistryComparisonSeed318.seed original w) c w) initial)
    (normalized (numbers (RegistryComparisonSeed318.seed original w) c w))
    (fallback (RegistryComparisonSeed318.seed original w) c w) column selected
    (by rw [group,flagValue]; exact value_boolean w column)
    (by unfold fallback
        rw [LegalAliasMeanings276.fallback_fixed _ _ column aliasOutside]
        unfold ZeroHintWordFrame303.flags
        rw [group])
  exact frame.trans (group.trans flagValue)
end ShielddSecurity.ComparisonBorrowFrame324

set_option pp.all true in
#check @ShielddSecurity.ComparisonBorrowFrame324.borrowColumns
#print axioms ShielddSecurity.ComparisonBorrowFrame324.borrowColumns

set_option pp.all true in
#check @ShielddSecurity.ComparisonBorrowFrame324.windows_checked
#print axioms ShielddSecurity.ComparisonBorrowFrame324.windows_checked

set_option pp.all true in
#check @ShielddSecurity.ComparisonBorrowFrame324.outside_assignments
#print axioms ShielddSecurity.ComparisonBorrowFrame324.outside_assignments

set_option pp.all true in
#check @ShielddSecurity.ComparisonBorrowFrame324.flag_frame
#print axioms ShielddSecurity.ComparisonBorrowFrame324.flag_frame

set_option pp.all true in
#check @ShielddSecurity.ComparisonBorrowFrame324.value
#print axioms ShielddSecurity.ComparisonBorrowFrame324.value

set_option pp.all true in
#check @ShielddSecurity.ComparisonBorrowFrame324.seed_value
#print axioms ShielddSecurity.ComparisonBorrowFrame324.seed_value

set_option pp.all true in
#check @ShielddSecurity.ComparisonBorrowFrame324.value_boolean
#print axioms ShielddSecurity.ComparisonBorrowFrame324.value_boolean

set_option pp.all true in
#check @ShielddSecurity.ComparisonBorrowFrame324.prepared_value
#print axioms ShielddSecurity.ComparisonBorrowFrame324.prepared_value

set_option pp.all true in
#check @ShielddSecurity.ComparisonBorrowFrame324.completed_value
#print axioms ShielddSecurity.ComparisonBorrowFrame324.completed_value
