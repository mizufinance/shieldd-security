"""Finite certificates for one block of the captured 64-field statement hash.

The complete thirteen-block inventory is checked before emitting a block. Each
block relates its actual rows to the independent permutation and its actual
predecessor state; the whole sponge theorem is a separate composition.
"""
from . import transfer_statement_hash_union as bundle, transfer_note_hash as hashes
from . import transfer_relation as relation
from .transfer_balance_rows import canonical, source_index
from .generate_hash_round import generate_selected_block, split_block_modules, linear, _signature_audits


def generate(manifest_data, page_data, extracted, accepted_roles, parameter_root, block_index):
    block_index = relation.natural(block_index, 13)
    bundle.validate(manifest_data, page_data, extracted, accepted_roles, parameter_root)
    first = None
    names = []
    target = None
    observed = None
    for ordinal, current in bundle.checked_pages(manifest_data, page_data, accepted_roles, parameter_root):
        obj = current['metadata']
        if first is None:
            first = obj
            observed = current['observed']
        if (len(first['hash']['inputs']) != 64 or first['hash']['domain'] != 34
                or current['block'] != ordinal - 1 or obj['hash'] != first['hash']):
            raise relation.RelationError('exact ordered thirteen-block 64-field statement hash')
        role = f"remaining{obj['slot']}.{obj['role']}{obj['level']}.permutation{obj['block']}"
        names.append('RuntimeHashBlock_' + role.replace('.', '_') + '_0')
        if ordinal == block_index + 1:
            target = current
    if len(names) != 13 or target is None:
        raise relation.RelationError('complete statement block inventory')
    del current
    base = 'RuntimeTransferStatementHashDomain34'
    part = target
    selected = hashes._select_permutation(part, extracted['parts'][str(block_index + 1)], parameter_root,
                                          role_prefix='remaining')
    if names[block_index] != 'RuntimeHashBlock_' + selected['calls'][0]['role'].replace('.', '_') + '_0':
        raise relation.RelationError('statement block namespace correspondence')
    body = generate_selected_block(part['metadata'], selected, selected['calls'][0]['role'], 0,
                                   part['metadata_sha256'], permutation_only=True)
    prefix = base + f'Block{block_index}'
    sources = split_block_modules(body, prefix, 5, linear_declarations_per_module=32)
    def value(ref):
        return observed[source_index(ref['source'])] if 'source' in ref else canonical([(0, int(ref['native'], 16))])
    inputs = [value(ref) for ref in first['hash']['inputs']]
    before = 'Poseidon.initialLinear 34 64' if block_index == 0 else names[block_index - 1] + '.states 65'
    source = f'import ShielddSecurity.{prefix}_Composition\n'
    if block_index:
        source += f'import ShielddSecurity.{base}Block{block_index - 1}_Composition\n'
    source += f'''set_option maxHeartbeats 800000
namespace ShielddSecurity.{prefix}Absorption
-- Actual statement block {block_index}; whole sponge/native/caller obligations remain separate.
def modulus : Nat := {relation.MODULUS}
def before : Poseidon.State Linear 6 := {before}
def inputs : List Linear := [''' + ', '.join(linear(lc) for lc in inputs[5 * block_index:5 * (block_index + 1)]) + f''']
theorem absorption : ∀ column : Fin 6,
    Compiler.canonical modulus ({names[block_index]}.states 0 column) =
      Compiler.canonical modulus (Poseidon.absorbLinear before inputs column) := by decide
theorem block_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho {names[block_index]}.rawRows) :
    (fun column => eval rho ({names[block_index]}.states 65 column)) =
      Poseidon.permute (Poseidon.castParameters {names[block_index]}.parameters)
        (Poseidon.absorb (fun column => eval rho (before column)) (inputs.map (eval rho))) := by
  have boundary : (fun column => eval rho ({names[block_index]}.states 0 column)) =
      Poseidon.absorb (fun column => eval rho (before column)) (inputs.map (eval rho)) := by
    calc
      _ = (fun column => eval rho (Poseidon.absorbLinear before inputs column)) := by
        funext column
        exact Compiler.canonical_equal rho _ _ (absorption column)
      _ = _ := Poseidon.eval_absorbLinear rho before inputs
  simpa only [boundary] using {names[block_index]}.permutation_sound rho one satisfied
#print axioms absorption
#print axioms block_sound
end ShielddSecurity.{prefix}Absorption
'''
    sources.append((prefix + 'Absorption', _signature_audits(source)))
    return sources
