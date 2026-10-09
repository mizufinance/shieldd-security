"""Symbolic composition for the actual captured EPK scopes two through five."""
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits


def generate(scope, page):
    if type(scope) is not int or not 2 <= scope <= 5:
        raise relation.RelationError("exact genuine remaining EPK scope required")
    if type(page) is not int or not 0 <= page < 8:
        raise relation.RelationError('exact EPK template page required')
    indices = list(range(max(1, page * 16), min(126, (page + 1) * 16)))
    sources = [f'RuntimeTransferEpk0FixedWindow{i:03d}TemplateCompletion' for i in indices]
    targets = [f'RuntimeTransferEpk{scope}RenamingRows{i:03d}' for i in indices]
    proofs = targets
    trace = f'RuntimeTransferEpk0FixedTemplatePage{page:02d}Trace'
    name = f'RuntimeTransferEpk{scope}TemplateRenamingPage{page:02d}'
    imports = list(dict.fromkeys([trace, *sources, *targets, *proofs]))
    text = ''.join(f'import ShielddSecurity.{module}\n' for module in imports)
    text += f'''namespace ShielddSecurity.{name}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

def sourceBlocks : List (List Row) := [{','.join(module + '.rawRows' for module in sources)}]
def targetBlocks : List (List Row) := [{','.join(module + '.rawRows' for module in targets)}]
def sourceRows : List Row := sourceBlocks.flatten
def targetRows : List Row := targetBlocks.flatten

theorem physical_program_rows : sourceRows = GroupFixedCircuitCompletion.rows
    (({trace}.windows 0).map GroupFixedTemplateTrace.Window.program) := rfl

variable {{F : Type}} [Field F]
    [CharP F 52435875175126190479447740508185965837690552500527637822603658699938581184513]

theorem sound (rho : Nat → F) (satisfied : Satisfies rho targetRows) :
    Satisfies (fun column => rho (RuntimeTransferEpk{scope}RenamingMap.columns column)) sourceRows := by
  intro row member
  obtain ⟨block,inside,present⟩ := List.mem_flatten.mp member
  simp only [sourceBlocks,List.mem_cons,List.not_mem_nil,or_false] at inside
  rcases inside with {' | '.join('rfl' for _ in indices)}
'''
    for source, target, proof in zip(sources, targets, proofs):
        text += f'''  · have localRows : Satisfies rho {target}.rawRows :=
      satisfies_block targetBlocks {target}.rawRows (by simp only [targetBlocks,List.mem_cons,List.not_mem_nil,or_false];tauto) rho satisfied
    exact {proof}.source_satisfied rho localRows row present
'''
    text += f'''
theorem complete (rho : Nat → F)
    (satisfied : Satisfies (fun column => rho (RuntimeTransferEpk{scope}RenamingMap.columns column)) sourceRows) :
    Satisfies rho targetRows := by
  intro row member
  obtain ⟨block,inside,present⟩ := List.mem_flatten.mp member
  simp only [targetBlocks,List.mem_cons,List.not_mem_nil,or_false] at inside
  rcases inside with {' | '.join('rfl' for _ in indices)}
'''
    for source, target, proof in zip(sources, targets, proofs):
        text += f'''  · have localRows : Satisfies (fun column => rho (RuntimeTransferEpk{scope}RenamingMap.columns column)) {source}.rawRows :=
      satisfies_block sourceBlocks {source}.rawRows (by simp only [sourceBlocks,List.mem_cons,List.not_mem_nil,or_false];tauto) _ satisfied
    exact {proof}.target_satisfied rho localRows row present
'''
    text += f'''
#print axioms physical_program_rows
#print axioms sound
#print axioms complete
end ShielddSecurity.{name}
'''
    return name, _signature_audits(text)
