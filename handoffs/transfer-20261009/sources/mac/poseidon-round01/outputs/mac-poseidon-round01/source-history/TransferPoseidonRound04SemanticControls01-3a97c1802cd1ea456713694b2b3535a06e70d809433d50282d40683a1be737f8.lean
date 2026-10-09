-- GENERATED instance of maintained round-semantic-controls-template.lean.txt.
import ShielddSecurity.TransferPoseidonRound04SemanticControlsData01
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.TransferPoseidonRound04SemanticControls01
open Compiler CompilerIndexed01 Poseidon PoseidonIndexedRound01
open TransferPoseidonRound04 TransferPoseidonRound04SemanticData01

open TransferPoseidonRound04SemanticControlsData01
theorem column_rejection (candidateRows : Array Row) (candidateParameters : Parameters Int 6)
    (candidateHints : Fin 6 → FifthHint)
    (rejected : checkColumn p copy candidateRows candidateParameters 4 before shifted transformed candidateHints 0=false) :
    productionCheck candidateRows candidateParameters after candidateHints=false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  simp only [productionCheck,Bool.and_eq_true] at accepted
  simp only [checkRound,Bool.and_eq_true] at accepted
  have column := List.all_eq_true.mp accepted.2.1 0 (List.mem_finRange 0)
  rw [rejected] at column
  contradiction

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticControls01.column_rejection
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticControls01.column_rejection

theorem ark_rejected : productionCheck originalRows alteredArk after fifthHints=false :=
  column_rejection originalRows alteredArk fifthHints ark_column_rejected
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticControls01.ark_rejected
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticControls01.ark_rejected

theorem wrong_hint_rejected : productionCheck originalRows parameters after alteredHint=false :=
  column_rejection originalRows parameters alteredHint hint_column_rejected
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticControls01.wrong_hint_rejected
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticControls01.wrong_hint_rejected

theorem coefficient_rejected : productionCheck changedRows parameters after fifthHints=false :=
  column_rejection changedRows parameters fifthHints row_column_rejected
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticControls01.coefficient_rejected
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticControls01.coefficient_rejected

theorem mix_rejection (candidateParameters : Parameters Int 6)
    (rejected : decide (canonical p (after 0)=canonical p (mixLinear candidateParameters.mds transformed 0))=false) :
    productionCheck originalRows candidateParameters after fifthHints=false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  simp only [productionCheck,Bool.and_eq_true,checkRound] at accepted
  have mix := List.all_eq_true.mp accepted.2.2 0 (List.mem_finRange 0)
  rw [rejected] at mix
  contradiction
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticControls01.mix_rejection
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticControls01.mix_rejection

theorem port_rejection (candidateAfter : State Linear 6)
    (rejected : decide (expressions (outputPorts 0)=Expression.linear (candidateAfter 0))=false) :
    productionCheck originalRows parameters candidateAfter fifthHints=false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  simp only [productionCheck,Bool.and_eq_true] at accepted
  have port := List.all_eq_true.mp accepted.1.2 0 (List.mem_finRange 0)
  rw [rejected] at port
  contradiction
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticControls01.port_rejection
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticControls01.port_rejection

theorem mds_rejected : productionCheck originalRows alteredMds after fifthHints=false :=
  mix_rejection alteredMds mds_mix_rejected
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticControls01.mds_rejected
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticControls01.mds_rejected

theorem state_port_rejected : productionCheck originalRows parameters alteredPort fifthHints=false :=
  port_rejection alteredPort port_binding_rejected
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticControls01.state_port_rejected
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticControls01.state_port_rejected

end ShielddSecurity.TransferPoseidonRound04SemanticControls01
