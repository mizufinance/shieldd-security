"""Compose captured statement blocks with a symbolic sponge recurrence."""
from . import transfer_statement_hash_union as bundle, transfer_relation as relation
from .transfer_balance_rows import canonical, source_index
from .generate_hash_round import linear, _signature_audits


def generate(manifest_data, page_data, extracted, accepted_roles, parameter_root):
    bundle.validate(manifest_data, page_data, extracted, accepted_roles, parameter_root)
    first = None
    names = []
    observed = None
    for ordinal, part in bundle.checked_pages(manifest_data, page_data, accepted_roles, parameter_root):
        obj = part['metadata']
        if first is None:
            first, observed = obj, part['observed']
        if (obj['hash'] != first['hash'] or part['block'] != ordinal - 1
                or len(obj['hash']['inputs']) != 64 or obj['hash']['domain'] != 34):
            raise relation.RelationError('complete ordered domain34 statement hash')
        role = f"remaining{obj['slot']}.{obj['role']}{obj['level']}.permutation{obj['block']}"
        names.append('RuntimeHashBlock_' + role.replace('.', '_') + '_0')
    if len(names) != 13:
        raise relation.RelationError('complete statement block count')
    def value(ref):
        return observed[source_index(ref['source'])] if 'source' in ref else canonical([(0, int(ref['native'], 16))])
    inputs = [value(ref) for ref in first['hash']['inputs']]
    base = 'RuntimeTransferStatementHashDomain34'
    layout = base + 'Layout'
    sources = []
    source = ''.join(f'import ShielddSecurity.{base}Block{i}_Data\n' for i in range(13))
    source += f'''set_option maxHeartbeats 800000
namespace ShielddSecurity.{layout}
def modulus : Nat := {relation.MODULUS}
def inputs : List Linear := [''' + ', '.join(map(linear, inputs)) + ']\n'
    source += f'def output : Linear := {linear(value(first["hash"]["output"]))}\n'
    for i in range(13):
        source += f'def chunk{i} : List Linear := [' + ', '.join(map(linear, inputs[5*i:5*(i+1)])) + ']\n'
    source += 'def chunks : List (List Linear) := [' + ', '.join(f'chunk{i}' for i in range(13)) + ']\n'
    source += 'def rowLists : List (List Row) := [' + ', '.join(name+'.rawRows' for name in names) + ']\n'
    source += 'def rawRows : List Row := rowLists.flatten\n'
    source += 'def states : Nat → Poseidon.State Linear 6 := fun index => match index with\n'
    source += '  | 0 => Poseidon.initialLinear 34 64\n'
    source += ''.join(f'  | {i+1} => {name}.states 65\n' for i, name in enumerate(names))
    source += '''  | _ => Poseidon.initialLinear 34 64
theorem chunk_order {F : Type} [Field F] (rho : Nat → F) :
    Poseidon.chunks5 (inputs.map (eval rho)) = chunks.map (fun chunk => chunk.map (eval rho)) := by rfl
#print axioms chunk_order
'''
    source += f'end ShielddSecurity.{layout}\n'
    sources.append((layout, _signature_audits(source)))
    for i, name in enumerate(names):
        step = base + f'Step{i}'
        # Keep the list-membership constructors explicit. Simplifying the
        # reflexive head equality changes it to True before rfl is applied.
        member = 'List.mem_cons.mpr (Or.inl rfl)'
        for _ in range(i):
            member = 'List.mem_cons.mpr (Or.inr (' + member + '))'
        source = f'''import ShielddSecurity.{layout}
import ShielddSecurity.{base}Block{i}Absorption
set_option maxHeartbeats 800000
namespace ShielddSecurity.{step}
theorem actual_step {{F : Type}} [Field F] [CharP F {layout}.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho {layout}.rawRows) :
    (fun column => eval rho ({layout}.states {i+1} column)) =
      Poseidon.permute (Poseidon.castParameters {names[0]}.parameters)
        (Poseidon.absorb (fun column => eval rho ({layout}.states {i} column))
          ({layout}.chunk{i}.map (eval rho))) := by
  have rows : Satisfies rho {name}.rawRows := by
    intro row contained
    apply satisfied row
    exact List.mem_flatten.mpr ⟨{name}.rawRows,
      (by unfold {layout}.rowLists; exact {member}), contained⟩
  have result := {base}Block{i}Absorption.block_sound rho one rows
  have parameters_equal : {name}.parameters = {names[0]}.parameters := rfl
  simpa only [parameters_equal, {layout}.states, {layout}.chunk{i},
    {base}Block{i}Absorption.before, {base}Block{i}Absorption.inputs] using result
#print axioms actual_step
end ShielddSecurity.{step}
'''
        sources.append((step, _signature_audits(source)))
    complete = base + 'Completion'
    source = 'import ShielddSecurity.PoseidonSpongeChain\n'
    source += ''.join(f'import ShielddSecurity.{base}Step{i}\n' for i in range(13))
    source += f'''set_option maxHeartbeats 800000
namespace ShielddSecurity.{complete}
-- Arbitrary satisfying assignment; the native/public-field caller correspondence is separate.
theorem actual_hash_sound {{F : Type}} [Field F] [CharP F {layout}.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho {layout}.rawRows) :
    eval rho {layout}.output = Poseidon.hash6 (Poseidon.castParameters {names[0]}.parameters)
      34 ({layout}.inputs.map (eval rho)) := by
  let states : Nat → Poseidon.State F 6 := fun index column => eval rho ({layout}.states index column)
  have transition : ∀ index value,
      (Poseidon.chunks5 ({layout}.inputs.map (eval rho)))[index]? = some value →
      states (index + 1) = Poseidon.permute (Poseidon.castParameters {names[0]}.parameters)
        (Poseidon.absorb (states index) value) := by
    intro index value member
    rw [{layout}.chunk_order] at member
    have bound : index < 13 := by
      obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp member
      simpa only [{layout}.chunks, List.length_map, List.length_cons, List.length_nil] using bound
    have alternatives : ''' + ' ∨ '.join(f'index = {i}' for i in range(13)) + ''' := by omega
    rcases alternatives with ''' + ' | '.join(f'index{i}' for i in range(13)) + '\n'
    for i in range(13):
        source += f'''    · subst index
      have chosen : value = {layout}.chunk{i}.map (eval rho) := by
        simpa only [{layout}.chunks, List.map_cons, List.map_nil,
          List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] using member.symm
      rw [chosen]
      exact {base}Step{i}.actual_step rho one satisfied
'''
    source += f'''  have nonempty : Poseidon.chunks5 ({layout}.inputs.map (eval rho)) ≠ [] := by
    rw [{layout}.chunk_order]
    intro empty
    have impossible := congrArg List.length empty
    change (13 : Nat) = 0 at impossible
    omega
  have initialState : states 0 = Poseidon.initial 34 ({layout}.inputs.map (eval rho)).length := by
    simpa only [states, {layout}.states, {layout}.inputs, List.length_map,
      List.length_cons, List.length_nil] using Poseidon.eval_initialLinear rho one 34 64
  have result := PoseidonSpongeChain.hash6_of_chain
    (Poseidon.castParameters {names[0]}.parameters) 34 ({layout}.inputs.map (eval rho))
    states nonempty initialState transition
  have output_equal : eval rho {layout}.output =
      eval rho ({names[12]}.states 65 ⟨1, by decide⟩) :=
    Compiler.canonical_equal rho _ _ (by decide)
  rw [{layout}.chunk_order] at result
  simpa only [{layout}.chunks, List.length_map, List.length_cons, List.length_nil,
    states, {layout}.states, ← output_equal] using result
#print axioms actual_hash_sound
end ShielddSecurity.{complete}
'''
    sources.append((complete, _signature_audits(source)))
    return sources
