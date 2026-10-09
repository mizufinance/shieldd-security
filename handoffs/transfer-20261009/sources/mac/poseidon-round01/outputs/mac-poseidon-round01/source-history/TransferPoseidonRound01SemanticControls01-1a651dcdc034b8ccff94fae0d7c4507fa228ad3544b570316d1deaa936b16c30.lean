-- GENERATED instance of maintained round-semantic-controls-template.lean.txt.
import ShielddSecurity.TransferPoseidonRound01SemanticProof01
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.TransferPoseidonRound01SemanticControls01
open Compiler CompilerIndexed01 Poseidon PoseidonIndexedRound01
open TransferPoseidonRound01 TransferPoseidonRound01SemanticData01

def alteredArk : Parameters Int 6 :=
  ⟨fun index column => parameters.ark index column + (if column.val=0 then 1 else 0),parameters.mds⟩
def alteredMds : Parameters Int 6 :=
  ⟨parameters.ark,fun row column => parameters.mds row column + (if row.val=0 ∧ column.val=0 then 1 else 0)⟩
def alteredPort (column : Fin 6) : Linear := if column.val=0 then after 1 else after column
def alteredHint (column : Fin 6) : FifthHint :=
  if column.val=0 then { fifthHints column with minus := (fifthHints column).first } else fifthHints column
def changedRow : Row := ⟨match row0.a with | [] => [] | (column,coefficient)::tail => (column,coefficient+1)::tail,row0.b⟩
def changedRows : Array Row := originalRows.modify 0 (fun _ => changedRow)

theorem ark_column_rejected : checkColumn p copy originalRows alteredArk 1 before shifted transformed fifthHints 0=false := by decide +kernel
theorem mds_mix_rejected : decide (canonical p (after 0)=canonical p (mixLinear alteredMds.mds transformed 0))=false := by decide +kernel
theorem hint_column_rejected : checkColumn p copy originalRows parameters 1 before shifted transformed alteredHint 0=false := by decide +kernel
theorem row_column_rejected : checkColumn p copy changedRows parameters 1 before shifted transformed fifthHints 0=false := by decide +kernel
theorem port_binding_rejected : decide (expressions (outputPorts 0)=Expression.linear (alteredPort 0))=false := by decide +kernel
theorem row_mutation_ran : changedRows[0]?=some changedRow ∧ changedRow≠row0 := by decide +kernel

theorem column_rejection (candidateRows : Array Row) (candidateParameters : Parameters Int 6)
    (candidateHints : Fin 6 → FifthHint)
    (rejected : checkColumn p copy candidateRows candidateParameters 1 before shifted transformed candidateHints 0=false) :
    productionCheck candidateRows candidateParameters after candidateHints=false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  simp only [productionCheck,Bool.and_eq_true] at accepted
  simp only [checkRound,Bool.and_eq_true] at accepted
  have column := List.all_eq_true.mp accepted.2.1 0 (List.mem_finRange 0)
  rw [rejected] at column
  contradiction

theorem ark_rejected : productionCheck originalRows alteredArk after fifthHints=false :=
  column_rejection _ _ _ ark_column_rejected
theorem wrong_hint_rejected : productionCheck originalRows parameters after alteredHint=false :=
  column_rejection _ _ _ hint_column_rejected
theorem coefficient_rejected : productionCheck changedRows parameters after fifthHints=false :=
  column_rejection _ _ _ row_column_rejected
theorem mds_rejected : productionCheck originalRows alteredMds after fifthHints=false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  simp only [productionCheck,Bool.and_eq_true,checkRound] at accepted
  have mix := List.all_eq_true.mp accepted.2.2 0 (List.mem_finRange 0)
  rw [mds_mix_rejected] at mix
  contradiction
theorem state_port_rejected : productionCheck originalRows parameters alteredPort fifthHints=false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  simp only [productionCheck,Bool.and_eq_true] at accepted
  have port := List.all_eq_true.mp accepted.1.2 0 (List.mem_finRange 0)
  rw [port_binding_rejected] at port
  contradiction
end ShielddSecurity.TransferPoseidonRound01SemanticControls01

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound01SemanticControls01.ark_column_rejected
#print axioms ShielddSecurity.TransferPoseidonRound01SemanticControls01.ark_column_rejected

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound01SemanticControls01.mds_mix_rejected
#print axioms ShielddSecurity.TransferPoseidonRound01SemanticControls01.mds_mix_rejected

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound01SemanticControls01.hint_column_rejected
#print axioms ShielddSecurity.TransferPoseidonRound01SemanticControls01.hint_column_rejected

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound01SemanticControls01.row_column_rejected
#print axioms ShielddSecurity.TransferPoseidonRound01SemanticControls01.row_column_rejected

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound01SemanticControls01.port_binding_rejected
#print axioms ShielddSecurity.TransferPoseidonRound01SemanticControls01.port_binding_rejected

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound01SemanticControls01.row_mutation_ran
#print axioms ShielddSecurity.TransferPoseidonRound01SemanticControls01.row_mutation_ran

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound01SemanticControls01.column_rejection
#print axioms ShielddSecurity.TransferPoseidonRound01SemanticControls01.column_rejection

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound01SemanticControls01.ark_rejected
#print axioms ShielddSecurity.TransferPoseidonRound01SemanticControls01.ark_rejected

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound01SemanticControls01.wrong_hint_rejected
#print axioms ShielddSecurity.TransferPoseidonRound01SemanticControls01.wrong_hint_rejected

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound01SemanticControls01.coefficient_rejected
#print axioms ShielddSecurity.TransferPoseidonRound01SemanticControls01.coefficient_rejected

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound01SemanticControls01.mds_rejected
#print axioms ShielddSecurity.TransferPoseidonRound01SemanticControls01.mds_rejected

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound01SemanticControls01.state_port_rejected
#print axioms ShielddSecurity.TransferPoseidonRound01SemanticControls01.state_port_rejected
