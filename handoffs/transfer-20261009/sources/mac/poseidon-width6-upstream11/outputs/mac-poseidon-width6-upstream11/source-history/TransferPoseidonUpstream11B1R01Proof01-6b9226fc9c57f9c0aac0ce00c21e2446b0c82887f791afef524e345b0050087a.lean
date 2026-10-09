set_option autoImplicit false
import ShielddSecurity.TransferPoseidonUpstream11B1R01ConsumerChecks01
import ShielddSecurity.TransferPoseidonUpstream11B1R01CoverageChecks01
import ShielddSecurity.TransferPoseidonUpstream11B1R01ProgramChecks01
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01
open Compiler CompilerIndexed01 CompilerCompletion Poseidon PoseidonIndexedFolded02 TransferPoseidonUpstream11B1R01
open TransferPoseidonUpstream11B1R01ConsumerChecks01 TransferPoseidonUpstream11B1R01CoverageChecks01 TransferPoseidonUpstream11B1R01ProgramChecks01

theorem column_cases (column : Fin 6) : column=0 ∨ column=1 ∨ column=2 ∨ column=3 ∨ column=4 ∨ column=5 := by
  have bound := column.isLt
  simp only [Fin.ext_iff]
  omega

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.column_cases
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.column_cases

theorem round_checked : checkRound p copy originalRows parameters 1 before shifted transformed after fifthHints=true := by
  simp only [checkRound,Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.mpr
    intro column _
    rcases column_cases column with rfl|rfl|rfl|rfl|rfl|rfl
    · exact column0_checked
    · exact column1_checked
    · exact column2_checked
    · exact column3_checked
    · exact column4_checked
    · exact column5_checked
  · apply List.all_eq_true.mpr
    intro column _
    simp only [decide_eq_true_eq]
    rcases column_cases column with rfl|rfl|rfl|rfl|rfl|rfl
    · exact mix0_checked
    · exact mix1_checked
    · exact mix2_checked
    · exact mix3_checked
    · exact mix4_checked
    · exact mix5_checked

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.round_checked
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.round_checked

theorem reverse_checked : checkOriginalCoverage p copy originalRows emittedRows rowMapping=true := by
  simp only [checkOriginalCoverage,Bool.and_eq_true]
  constructor
  · decide +kernel
  · apply List.all_eq_true.mpr
    intro index member
    have bound := List.mem_range.mp member
    rw [rows_shape.1] at bound
    have cases : index=0 ∨ index=1 ∨ index=2 ∨ index=3 ∨ index=4 ∨ index=5 ∨ index=6 ∨ index=7 ∨ index=8 ∨ index=9 ∨ index=10 ∨ index=11 ∨ index=12 ∨ index=13 ∨ index=14 ∨ index=15 ∨ index=16 ∨ index=17 ∨ index=18 ∨ index=19 ∨ index=20 ∨ index=21 ∨ index=22 ∨ index=23 ∨ index=24 := by omega
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact row0_checked
    · exact row1_checked
    · exact row2_checked
    · exact row3_checked
    · exact row4_checked
    · exact row5_checked
    · exact row6_checked
    · exact row7_checked
    · exact row8_checked
    · exact row9_checked
    · exact row10_checked
    · exact row11_checked
    · exact row12_checked
    · exact row13_checked
    · exact row14_checked
    · exact row15_checked
    · exact row16_checked
    · exact row17_checked
    · exact row18_checked
    · exact row19_checked
    · exact row20_checked
    · exact row21_checked
    · exact row22_checked
    · exact row23_checked
    · exact row24_checked

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.reverse_checked
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.reverse_checked

theorem production_checked : productionCheck originalRows parameters before after fifthHints rowMapping=true := by
  simp only [productionCheck,Bool.and_eq_true]
  exact ⟨⟨⟨actual_copy_checked,round_checked⟩,reverse_checked⟩,cut_support_checked⟩

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.production_checked
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.production_checked

theorem checked_fields (rows : Array Row) (candidate : Parameters Int 6)
    (candidateBefore candidateAfter : State Linear 6) (hints : Fin 6 → FifthHint) (mapping : Array Nat)
    (accepted : productionCheck rows candidate candidateBefore candidateAfter hints mapping=true) :
    checkRowAt p rows 24 ⟨[(0,1),(copy,-1)],[]⟩=true ∧
    checkRound p copy rows candidate 1 candidateBefore shifted transformed candidateAfter hints=true ∧
    checkOriginalCoverage p copy rows emittedRows mapping=true ∧
    CompilerPriorFrame01.checkSupport 6 (cutTerms candidateBefore) steps=true := by
  simp only [productionCheck,Bool.and_eq_true] at accepted
  exact ⟨accepted.1.1.1,accepted.1.1.2,accepted.1.2,accepted.2⟩

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.checked_fields
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.checked_fields

theorem ordered : Topological [0,copy] [] steps := CompilerOrder.checked_order _ _ _ ordered_checked

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.ordered
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.ordered

theorem write_bounds (column : Nat) (member : column∈PoseidonCompletion.writes steps) : 61218≤column ∧ column≤61241 :=
  of_decide_eq_true (List.all_eq_true.mp writes_checked column member)

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.write_bounds
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.write_bounds

theorem raw_support_bound (row : Row) (member : row∈originalRows.toList)
    (term : Nat × Int) (support : term∈row.a++row.b) : term.1≤61241 ∨ term.1=copy :=
  of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp raw_support_checked row member) term support)

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.raw_support_bound
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.raw_support_bound

theorem round_certificate : RoundCertificate p (unoutlineRows copy originalRows.toList) parameters 1 before shifted transformed after :=
  checkRound_sound p copy originalRows parameters 1 before shifted transformed after fifthHints round_checked

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.round_certificate
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.round_certificate

variable {F : Type} [Field F] [CharP F p]

def completed (base : Nat → F) : Nat → F := run base steps

theorem legal (base : Nat → F) : Legal base steps := by
  simp [steps,materializedSteps,copyStep,Legal,Step.Legal]

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.legal
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.legal

theorem original_columns_preserved (base : Nat → F) (column : Nat) (bound : column<22738) : completed base column=base column := by
  apply PoseidonCompletion.run_outside
  intro member
  have bounds := write_bounds column member
  omega

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.original_columns_preserved
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.original_columns_preserved

theorem copy_preserved (base : Nat → F) : completed base copy=base copy :=
  run_preserves base steps [0,copy] [] ordered copy (by simp)

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.copy_preserved
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.copy_preserved

theorem checked_sound (rows : Array Row) (candidate : Parameters Int 6)
    (candidateBefore candidateAfter : State Linear 6) (hints : Fin 6 → FifthHint) (mapping : Array Nat)
    (accepted : productionCheck rows candidate candidateBefore candidateAfter hints mapping=true)
    (rho : Nat → F) (one : rho 0=1) (four : (4:F)≠0) (satisfied : Satisfies rho rows.toList) :
    (fun column => eval rho (candidateAfter column)) =
      Poseidon.round (castParameters candidate) 1 (fun column => eval rho (candidateBefore column)) := by
  have fields := checked_fields rows candidate candidateBefore candidateAfter hints mapping accepted
  have unoutlined := unoutline_rows_sound rho copy rows.toList satisfied
    (checkRowAt_sound p rows 24 _ fields.1)
  exact round_certificate_sound rho (unoutlineRows copy rows.toList) candidate 1
    candidateBefore shifted transformed candidateAfter one four unoutlined
    (checkRound_sound p copy rows candidate 1 candidateBefore shifted transformed candidateAfter hints fields.2.1)

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.checked_sound
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.checked_sound

theorem checked_constructive (rows : Array Row) (candidate : Parameters Int 6)
    (candidateBefore candidateAfter : State Linear 6) (hints : Fin 6 → FifthHint) (mapping : Array Nat)
    (accepted : productionCheck rows candidate candidateBefore candidateAfter hints mapping=true)
    (base : Nat → F) (one : base 0=1) (linked : base copy=base 0) (four : (4:F)≠0) :
    Satisfies (completed base) rows.toList ∧
    (∀ column<22738,completed base column=base column) ∧
    completed base copy=base copy ∧
    (fun column => eval (completed base) (candidateBefore column))=(fun column => eval base (candidateBefore column)) ∧
    (fun column => eval (completed base) (candidateAfter column))=
      Poseidon.round (castParameters candidate) 1 (fun column => eval base (candidateBefore column)) := by
  have fields := checked_fields rows candidate candidateBefore candidateAfter hints mapping accepted
  have coverage : ∀ actual∈rows.toList,∃ expected∈emitted steps,
      canonical p (unoutline copy actual.a)=canonical p expected.a ∧ canonical p (unoutline copy actual.b)=canonical p expected.b := by
    simpa [emittedRows] using checkOriginalCoverage_sound p copy rows emittedRows mapping fields.2.2.1
  have satisfied := (original_rows_complete base steps [0,copy] rows.toList copy ordered (legal base)
    (by simp) (by simp) linked coverage).1
  have frame : (fun column : Fin 6 => eval (completed base) (candidateBefore column))=(fun column => eval base (candidateBefore column)) := by
    funext column
    simpa [cutTerms,column.isLt] using CompilerPriorFrame01.completed_inputs 6 (cutTerms candidateBefore) steps fields.2.2.2 base column.val column.isLt
  have result := checked_sound rows candidate candidateBefore candidateAfter hints mapping accepted
    (completed base) ((original_columns_preserved base 0 (by decide)).trans one) four satisfied
  rw [frame] at result
  exact ⟨satisfied,original_columns_preserved base,copy_preserved base,frame,result⟩

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.checked_constructive
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.checked_constructive

theorem arbitrary_native_round (rho : Nat → F) (one : rho 0=1) (four : (4:F)≠0) (satisfied : Satisfies rho originalRows.toList) :
    (fun column => eval rho (after column))=Poseidon.round (castParameters parameters) 1 (fun column => eval rho (before column)) :=
  checked_sound _ _ _ _ _ _ production_checked rho one four satisfied

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.arbitrary_native_round
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.arbitrary_native_round

theorem total_native_round (base : Nat → F) (one : base 0=1) (linked : base copy=base 0) (four : (4:F)≠0) :
    Satisfies (completed base) originalRows.toList ∧
    (∀ column<22738,completed base column=base column) ∧
    completed base copy=base copy ∧
    (fun column => eval (completed base) (before column))=(fun column => eval base (before column)) ∧
    (fun column => eval (completed base) (after column))=Poseidon.round (castParameters parameters) 1 (fun column => eval base (before column)) :=
  checked_constructive _ _ _ _ _ _ production_checked base one linked four
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.total_native_round
#print axioms ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01.total_native_round

end ShielddSecurity.TransferPoseidonUpstream11B1R01Proof01
