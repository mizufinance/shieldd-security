-- GENERATED instance of maintained round-semantic-controls-template.lean.txt.
import ShielddSecurity.TransferPoseidonRound01SemanticProof01
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.TransferPoseidonRound01SemanticControlsData01
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
def changedRows : Array Row := Array.mk [changedRow,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11,row12,row13,row14,row15,row16,row17,row18,row19,row20,row21,row22,row23,row24]

theorem ark_column_rejected : checkColumn p copy originalRows alteredArk 1 before shifted transformed fifthHints 0=false := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound01SemanticControlsData01.ark_column_rejected
#print axioms ShielddSecurity.TransferPoseidonRound01SemanticControlsData01.ark_column_rejected

theorem mds_mix_rejected : decide (canonical p (after 0)=canonical p (mixLinear alteredMds.mds transformed 0))=false := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound01SemanticControlsData01.mds_mix_rejected
#print axioms ShielddSecurity.TransferPoseidonRound01SemanticControlsData01.mds_mix_rejected

theorem hint_column_rejected : checkColumn p copy originalRows parameters 1 before shifted transformed alteredHint 0=false := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound01SemanticControlsData01.hint_column_rejected
#print axioms ShielddSecurity.TransferPoseidonRound01SemanticControlsData01.hint_column_rejected

theorem row_column_rejected : checkColumn p copy changedRows parameters 1 before shifted transformed fifthHints 0=false := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound01SemanticControlsData01.row_column_rejected
#print axioms ShielddSecurity.TransferPoseidonRound01SemanticControlsData01.row_column_rejected

theorem port_binding_rejected : decide (expressions (outputPorts 0)=Expression.linear (alteredPort 0))=false := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound01SemanticControlsData01.port_binding_rejected
#print axioms ShielddSecurity.TransferPoseidonRound01SemanticControlsData01.port_binding_rejected

theorem row_mutation_ran : changedRows[0]?=some changedRow ∧ changedRow≠row0 ∧ changedRows.toList.tail=originalRows.toList.tail := by decide +kernel

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound01SemanticControlsData01.row_mutation_ran
#print axioms ShielddSecurity.TransferPoseidonRound01SemanticControlsData01.row_mutation_ran

end ShielddSecurity.TransferPoseidonRound01SemanticControlsData01
