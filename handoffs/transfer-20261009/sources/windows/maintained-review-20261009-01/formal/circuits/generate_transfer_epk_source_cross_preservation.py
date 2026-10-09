"""Original EPK rows preserved by separately captured target-scope write patches."""
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits


def _names(writer):
    if type(writer) is not int or not 1 <= writer <= 5:
        raise relation.RelationError('genuine target EPK writer required')
    supports=[f'RuntimeTransferEpk0ConstructiveOwnSupportCanonicalPart{i:02d}' for i in range(16)]
    supports+=['RuntimeTransferEpk0ConstructiveOwnSupportCanonicalTail','RuntimeTransferEpk0ConstructiveOwnSupportFirst']
    supports+=[f'RuntimeTransferEpk0ConstructiveOwnSupportPage{i:02d}' for i in range(8)]
    supports+=['RuntimeTransferEpk0ConstructiveOwnSupportPublication']
    return supports,f'RuntimeTransferEpk{writer}ConstructiveWriteTree'


def generate_block(writer,index):
    supports,tree=_names(writer)
    if type(index) is not int or not 0<=index<27:
        raise relation.RelationError('exact bounded original EPK row block required')
    block=supports[index];name=f'RuntimeTransferEpk0PreservedBy{writer}Block{index:02d}'
    text=f'''import ShielddSecurity.{block}
import ShielddSecurity.{tree}
namespace ShielddSecurity.{name}
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

def rows : List Row := {block}.rows

theorem outside_checked : rows.all (fun row => (row.a ++ row.b).all (fun term =>
    decide (FiniteColumnRenaming.lookup {tree}.tree term.1 = none))) = true := by decide

theorem outside : ∀ row ∈ rows,∀ term ∈ row.a ++ row.b,
    FiniteColumnRenaming.lookup {tree}.tree term.1 = none := by
  intro row member term present
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp outside_checked row member) term present)

#print axioms outside_checked
#print axioms outside
end ShielddSecurity.{name}
'''
    return name,_signature_audits(text)


def generate_join(writer):
    supports,tree=_names(writer)
    blocks=[f'RuntimeTransferEpk0PreservedBy{writer}Block{i:02d}' for i in range(27)]
    patch=f'TransferEpkScope{writer}PatchedCompletion';name=f'TransferEpkScope0PreservedBy{writer}'
    text=''.join(f'import ShielddSecurity.{dep}\n' for dep in [patch,'TransferEpkScope0PatchedCompletion',*blocks])
    text+=f'''namespace ShielddSecurity.{name}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

def blocks : List (List Row) := [{','.join(block+'.rows' for block in blocks)}]

private theorem blocks_rows : blocks.flatten = TransferEpkScope0Relation.rows := by
  rw [TransferEpkScope0Relation.rows,TransferEpkCanonicalFixedRelation.rows,
    TransferEpkScope1Relation.source_fixed_rows]
  simp only [blocks,List.flatten_cons,List.flatten_nil,List.append_nil,
    {','.join(block+'.rows' for block in blocks)},
    {','.join(support+'.rows' for support in supports)},
    RuntimeTransferEpk0Canonical.originalRows,RuntimeTransferEpk0Canonical.originalBlocks,
    TransferEpkScope1Relation.sourceBlocks,List.append_assoc]

theorem rows_outside : ∀ row ∈ TransferEpkScope0Relation.rows,∀ term ∈ row.a ++ row.b,
    FiniteColumnRenaming.lookup {tree}.tree term.1 = none := by
  have each (block : List Row) (member : block ∈ blocks) :
      ∀ row ∈ block,∀ term ∈ row.a ++ row.b,
        FiniteColumnRenaming.lookup {tree}.tree term.1 = none := by
    simp only [blocks,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with {' | '.join('rfl' for _ in blocks)}
'''
    for block in blocks:text+=f'    · exact {block}.outside\n'
    text+=f'''  intro row member term present
  rw [← blocks_rows] at member
  obtain ⟨block,inside,contained⟩ := List.mem_flatten.mp member
  exact each block inside row contained term present

theorem native_inputs_outside : [0,200692,4930].all (fun column =>
    decide (FiniteColumnRenaming.lookup {tree}.tree column = none)) = true := by decide

theorem preserves_rows {{F : Type}} [Field F]
    [CharP F 52435875175126190479447740508185965837690552500527637822603658699938581184513]
    (rho : Nat → F) (n : Nat) (satisfied : Satisfies rho TransferEpkScope0Relation.rows) :
    Satisfies ({patch}.construct rho n) TransferEpkScope0Relation.rows :=
  {patch}.prior_rows rho n TransferEpkScope0Relation.rows rows_outside satisfied

#print axioms rows_outside
#print axioms native_inputs_outside
#print axioms preserves_rows
end ShielddSecurity.{name}
'''
    return name,_signature_audits(text)
