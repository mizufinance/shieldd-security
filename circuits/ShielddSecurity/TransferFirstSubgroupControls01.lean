import ShielddSecurity.TransferFirstSubgroupCertificates01

set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.TransferFirstSubgroupControls01
open Compiler CompilerIndexed01 TransferFirstSubgroupData01 TransferFirstSubgroupCertificates01

def coefficientMutation : Array Row := originalRows.set! 0 ⟨[(16,2)], row0.b⟩
theorem coefficient_rejected : checkRowAt p coefficientMutation 0 row0 = false := by decide +kernel

def wrongExistingRow : Hint 22 := match hints ⟨22,by decide⟩ with
  | .square left right x y output _ => .square left right x y output 1
  | other => other

theorem existing_row_rejected :
    checkNode p copy arithmeticRows inputTerms (graph.prior expressions ⟨22,by decide⟩) wrongExistingRow = false := by
  decide +kernel

def rewired (index : Fin 80) : Hint index.val :=
  if changed : index.val=22 then
    match hints index with
    | .square _ _ x y output row => .square ⟨3,by omega⟩ ⟨3,by omega⟩ x y output row
    | other => other
  else hints index

theorem rewired_port_rejected :
    checkBlock p copy arithmeticRows inputTerms graph expressions rewired TransferFirstSubgroupLeaf01.indices = false := by
  decide +kernel

theorem missing_reverse_coverage_rejected :
    checkOriginalCoverage p copy originalRows emittedOriginal ((List.range 70).toArray) = false := by decide +kernel

def wrongInputTerms (input : Nat) : Linear := if input=13 then [(17,1)] else inputTerms input

theorem wrong_input_terms_rejected :
    checkBlock p copy arithmeticRows wrongInputTerms graph expressions hints TransferFirstSubgroupLeaf01.indices = false := by
  decide +kernel

theorem wrong_copy_column_rejected :
    checkRowAt p originalRows 70 ⟨[(0,1),(200691,-1)],[]⟩ = false := by decide +kernel

theorem missing_copy_row_rejected :
    checkRowAt p (originalRows.extract 0 70) 70 ⟨[(0,1),(copy,-1)],[]⟩ = false := by decide +kernel

theorem full_index_coverage_accepted :
    CompilerIndexCoverage01.checkCoverage (TransferFirstSubgroupLeaf01.indices ++ TransferFirstSubgroupLeaf02.indices)=true := by decide +kernel

theorem omitted_node_rejected :
    CompilerIndexCoverage01.checkCoverage ((TransferFirstSubgroupLeaf01.indices ++ TransferFirstSubgroupLeaf02.indices).filter (fun i => i.val≠79))=false := by
  decide +kernel

end ShielddSecurity.TransferFirstSubgroupControls01

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupControls01.coefficient_rejected
#print axioms ShielddSecurity.TransferFirstSubgroupControls01.coefficient_rejected

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupControls01.existing_row_rejected
#print axioms ShielddSecurity.TransferFirstSubgroupControls01.existing_row_rejected

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupControls01.rewired_port_rejected
#print axioms ShielddSecurity.TransferFirstSubgroupControls01.rewired_port_rejected

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupControls01.missing_reverse_coverage_rejected
#print axioms ShielddSecurity.TransferFirstSubgroupControls01.missing_reverse_coverage_rejected

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupControls01.wrong_input_terms_rejected
#print axioms ShielddSecurity.TransferFirstSubgroupControls01.wrong_input_terms_rejected

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupControls01.wrong_copy_column_rejected
#print axioms ShielddSecurity.TransferFirstSubgroupControls01.wrong_copy_column_rejected

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupControls01.missing_copy_row_rejected
#print axioms ShielddSecurity.TransferFirstSubgroupControls01.missing_copy_row_rejected

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupControls01.full_index_coverage_accepted
#print axioms ShielddSecurity.TransferFirstSubgroupControls01.full_index_coverage_accepted

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupControls01.omitted_node_rejected
#print axioms ShielddSecurity.TransferFirstSubgroupControls01.omitted_node_rejected
