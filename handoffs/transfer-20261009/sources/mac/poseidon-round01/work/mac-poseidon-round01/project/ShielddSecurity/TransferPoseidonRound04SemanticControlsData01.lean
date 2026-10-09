-- GENERATED instance of maintained round-semantic-controls-template.lean.txt.
import ShielddSecurity.TransferPoseidonRound04SemanticProof01
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.TransferPoseidonRound04SemanticControlsData01
open Compiler CompilerIndexed01 Poseidon PoseidonIndexedRound01
open TransferPoseidonRound04 TransferPoseidonRound04SemanticData01

def alteredArk : Parameters Int 6 :=
  ⟨fun index column => parameters.ark index column + (if column.val=0 then 1 else 0),parameters.mds⟩
def alteredMds : Parameters Int 6 :=
  ⟨parameters.ark,fun row column => parameters.mds row column + (if row.val=0 ∧ column.val=0 then 1 else 0)⟩
def alteredPort (column : Fin 6) : Linear := if column.val=0 then after 1 else after column
def alteredHint (column : Fin 6) : FifthHint :=
  if column.val=0 then { fifthHints column with minus := (fifthHints column).first } else fifthHints column
def changedRow : Row := ⟨match row0.a with | [] => [] | (column,coefficient)::tail => (column,coefficient+1)::tail,row0.b⟩
def changedRows : Array Row := Array.mk [changedRow,row1,row2,row3,row4]

theorem ark_column_rejected : checkColumn p copy originalRows alteredArk 4 before shifted transformed fifthHints 0=false := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticControlsData01.ark_column_rejected
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticControlsData01.ark_column_rejected

theorem mds_mix_rejected : decide (canonical p (after 0)=canonical p (mixLinear alteredMds.mds transformed 0))=false := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticControlsData01.mds_mix_rejected
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticControlsData01.mds_mix_rejected

theorem hint_column_rejected : checkColumn p copy originalRows parameters 4 before shifted transformed alteredHint 0=false := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticControlsData01.hint_column_rejected
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticControlsData01.hint_column_rejected

theorem row_column_rejected : checkColumn p copy changedRows parameters 4 before shifted transformed fifthHints 0=false := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticControlsData01.row_column_rejected
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticControlsData01.row_column_rejected

theorem port_binding_rejected : decide (expressions (outputPorts 0)=Expression.linear (alteredPort 0))=false := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticControlsData01.port_binding_rejected
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticControlsData01.port_binding_rejected

theorem row_mutation_ran : changedRows[0]?=some changedRow ∧ changedRow≠row0 ∧ changedRows.toList.tail=originalRows.toList.tail := by decide +kernel

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticControlsData01.row_mutation_ran
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticControlsData01.row_mutation_ran

end ShielddSecurity.TransferPoseidonRound04SemanticControlsData01
