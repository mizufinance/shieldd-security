"""Bounded captured EPK row supports for preservation by later write patches."""
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits


def _names(prior, writer):
    if type(prior) is not int or type(writer) is not int or not 1 <= prior < writer <= 5:
        raise relation.RelationError('ordered distinct actual EPK scopes required')
    supports = [f'RuntimeTransferEpk{prior}ConstructiveOwnSupportCanonicalPart{i:03d}' for i in range(6)]
    supports += [f'RuntimeTransferEpk{prior}ConstructiveOwnSupportFirst']
    supports += [f'RuntimeTransferEpk{prior}ConstructiveOwnSupportPage{i:02d}' for i in range(8)]
    supports += [f'RuntimeTransferEpk{prior}ConstructiveOwnSupportPublication']
    return supports, f'RuntimeTransferEpk{writer}ConstructiveWriteTree'


def generate_block(prior, writer, index):
    supports, tree = _names(prior, writer)
    if type(index) is not int or not 0 <= index < len(supports):
        raise relation.RelationError('exact bounded prior-row block required')
    block = supports[index]
    name = f'RuntimeTransferEpk{prior}PreservedBy{writer}Block{index:02d}'
    text = f'''import ShielddSecurity.{block}
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
    return name, _signature_audits(text)


def generate_join(prior, writer, prior_pair):
    supports, tree = _names(prior, writer)
    if prior_pair.get('scope_id') != prior:
        raise relation.RelationError('genuine prior EPK roles required')
    columns = dict(prior_pair['restricted_map'])
    private = columns[4930]
    blocks = [f'RuntimeTransferEpk{prior}PreservedBy{writer}Block{i:02d}' for i in range(16)]
    patch = f'TransferEpkScope{writer}PatchedCompletion'
    prior_completion = f'TransferEpkScope{prior}PatchedCompletion'
    prior_relation = f'TransferEpkScope{prior}Relation'
    name = f'TransferEpkScope{prior}PreservedBy{writer}'
    text = ''.join(f'import ShielddSecurity.{dep}\n' for dep in [patch, prior_completion, *blocks])
    text += f'''namespace ShielddSecurity.{name}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

def blocks : List (List Row) := [{','.join(block+'.rows' for block in blocks)}]

private theorem blocks_rows : blocks.flatten = {prior_relation}.rows := by
  simp only [blocks,List.flatten_cons,List.flatten_nil,List.append_nil,
    {','.join(block+'.rows' for block in blocks)},
    {','.join(support+'.rows' for support in supports)},
    {prior_relation}.rows,{prior_relation}.relationRows,{prior_relation}.targetBlocks,
    RuntimeTransferEpk{prior}RenamingRows126.rawRows,List.append_assoc]

theorem rows_outside : ∀ row ∈ {prior_relation}.rows,∀ term ∈ row.a ++ row.b,
    FiniteColumnRenaming.lookup {tree}.tree term.1 = none := by
  have each (block : List Row) (member : block ∈ blocks) :
      ∀ row ∈ block,∀ term ∈ row.a ++ row.b,
        FiniteColumnRenaming.lookup {tree}.tree term.1 = none := by
    simp only [blocks,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with {' | '.join('rfl' for _ in blocks)}
'''
    for block in blocks:
        text += f'    · exact {block}.outside\n'
    text += f'''  intro row member term present
  rw [← blocks_rows] at member
  obtain ⟨block,inside,contained⟩ := List.mem_flatten.mp member
  exact each block inside row contained term present

theorem native_inputs_outside : [0,200692,{private}].all (fun column =>
    decide (FiniteColumnRenaming.lookup {tree}.tree column = none)) = true := by decide

theorem preserves_rows {{F : Type}} [Field F]
    [CharP F 52435875175126190479447740508185965837690552500527637822603658699938581184513]
    (rho : Nat → F) (n : Nat) (satisfied : Satisfies rho {prior_relation}.rows) :
    Satisfies ({patch}.construct rho n) {prior_relation}.rows :=
  {patch}.prior_rows rho n {prior_relation}.rows rows_outside satisfied

#print axioms rows_outside
#print axioms native_inputs_outside
#print axioms preserves_rows
end ShielddSecurity.{name}
'''
    return name, _signature_audits(text)
