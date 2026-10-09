"""Generate actual-row Poseidon round, block, and explicit hash compositions.

Each generated theorem states its own boundary. Whole-hash composition checks
absorption, adjacent blocks, domain/arity and the actual output coordinate.
"""
import hashlib
import re
from pathlib import Path
import sys
try:
    from .hash_rows import select
    from .poseidon_graph import P, decode_json
except ImportError:
    from hash_rows import select
    from poseidon_graph import P, decode_json


def _signature_audits(source):
    """Emit complete named statements once, including nested generated modules."""
    def emit(match):
        check = 'set_option pp.all true in\n#check @'+match[1]+'\n'
        if source[:match.start()].endswith(check):
            return match[0]
        return check+match[0]
    return re.sub(r'^#print axioms ([A-Za-z0-9_]+)$', emit,
                  source, flags=re.MULTILINE)


def signed(value):
    return value if value <= P // 2 else value - P


def linear(terms):
    return '[' + ', '.join(f'({column}, ({signed(value)} : Int))' for column, value in terms) + ']'


def finite_function(values, render, fallback):
    return 'fun column => match column.val with\n' + '\n'.join(
        f'  | {i} => {render(value)}' for i, value in enumerate(values)) + f'\n  | _ => {fallback}'


def generate(export, parameter_root, role, chunk, index, export_hash):
    selected = select(export, parameter_root)
    return generate_selected_round(export,selected,role,chunk,index,export_hash)


def generate_selected_round(export, selected, role, chunk, index, export_hash):
    """Emit one finite round from checked selection; the kernel checks every row."""
    calls = [call for call in selected['calls'] if call['role'] == role]
    if len(calls) != 1:
        raise ValueError('missing/ambiguous requested hash role')
    call = calls[0]
    segments = [segment for segment in call['segments'] if segment['kind'] == 'round'
                and segment['chunk'] == chunk and segment['index'] == index]
    if len(segments) != 1:
        raise ValueError('missing/ambiguous requested hash round')
    segment, params = segments[0], call['parameters']
    width = params['width']
    indices = sorted(set(segment['rows']) | {selected['constant_link']})
    rows = [selected['rows'][i] for i in indices]
    name = role.replace('.', '_') + f'_{chunk}_{index}'
    out = [f'''import ShielddSecurity.Poseidon
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeHashRound_{name}
-- Exact emitted export SHA256: {export_hash}
-- Full relation digest (extraction TCB): {export['relation_digest']}
-- Original row indices: {indices}
-- Only round {index}, chunk {chunk}, role {role}; NOT complete hash soundness.
def modulus : Nat := {P}
def rawRows : List Row := [
''']
    out.append(',\n'.join('  ⟨' + linear(a) + ', ' + linear(b) + '⟩' for a, b in rows))
    out.append(f''']
def rows : List Row := Compiler.unoutlineRows {selected['outline']} rawRows
-- The round vector is the exact selected artifact row. Values of ark at other
-- round indices are deliberately not a whole-permutation parameter claim.
def parameters : Poseidon.Parameters Int {width} where
  ark := fun _ => {finite_function(params['ark'][index], lambda v: str(signed(v)), '0').replace(chr(10), chr(10)+'  ')}
  mds := fun row => match row.val with
''')
    for i, matrix_row in enumerate(params['mds']):
        rendered = finite_function(matrix_row, lambda v: str(signed(v)), '0').replace('\n', '\n    ')
        out.append(f'  | {i} => {rendered}\n')
    out.append('  | _ => fun _ => 0\n')
    for state in ['before', 'shifted', 'transformed', 'after']:
        out.append(f'def {state} : Poseidon.State Linear {width} :=\n  '
                   + finite_function(segment[state], linear, '[]').replace('\n', '\n  ') + '\n')
    out.append(f'''
theorem certificate : Poseidon.RoundCertificate modulus rows parameters {index}
    before shifted transformed after := by
  constructor
  · decide
  · ''')
    # Fin.cases is core dependent elimination: no optional tactic dependency and
    # no enumeration of field assignments. All remaining checks are finite data.
    for i in range(width):
        indent = '    ' + '  ' * i
        out.append('refine Fin.cases ?_ ?_\n')
        out.append(indent + '· intro active\n')
        cert = segment['fifths'].get(i)
        if cert is None:
            out.append(indent + '  change false = true at active\n')
            out.append(indent + '  cases active\n')
        elif cert['kind'] == 'constant':
            out.append(indent + '  apply Poseidon.FifthCertificate.constant '
                       + f'({signed(cert["coefficient"])} : Int) <;> decide\n')
        else:
            out.append(indent + '  apply Poseidon.FifthCertificate.arithmetic '
                       + ' '.join(linear(cert[key]) for key in ['square', 'fourth', 'auxiliary'])
                       + ' <;> decide\n')
        out.append(indent + '· ')
    out.append('intro impossible; exact Fin.elim0 impossible\n  · decide\n  · decide\n')
    out.append(f'''
theorem actual_round_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    (fun column => eval rho (after column)) =
      Poseidon.round (Poseidon.castParameters parameters) {index}
        (fun column => eval rho (before column)) := by
  have four : (4 : F) ≠ 0 := by
    intro zero
    have impossible : (4 : Nat) = 0 := bounded_cast_injective (F := F) (p := modulus)
      (by decide) (by decide) (by simpa using zero)
    omega
  have normalized : Satisfies rho rows :=
    Compiler.unoutline_rows_sound rho {selected['outline']} rawRows satisfied (by decide)
  exact Poseidon.round_certificate_sound rho rows parameters {index}
    before shifted transformed after one four normalized certificate

#print axioms certificate
#print axioms actual_round_sound
end ShielddSecurity.RuntimeHashRound_{name}
''')
    return _signature_audits(''.join(out))


def round_constructor(segment, width, indent, render_linear=linear):
    """Finite local data checks; no quantified field assignments are enumerated."""
    out = ['constructor\n', indent + '· decide\n', indent + '· ']
    index = segment['index']
    for column in range(width):
        nested = indent + '  ' + '  ' * column
        out.extend(['refine Fin.cases ?_ ?_\n', nested + '· intro active\n'])
        cert = segment['fifths'].get(column)
        if cert is None:
            out.append(nested + '  change false = true at active\n')
            out.append(nested + '  cases active\n')
        elif cert['kind'] == 'constant':
            out.append(nested + f'  apply Poseidon.FifthCertificate.constant ({signed(cert["coefficient"])} : Int) <;> decide\n')
        else:
            out.append(nested + '  apply Poseidon.FifthCertificate.arithmetic '
                       + ' '.join(render_linear(cert[key]) for key in ('square', 'fourth', 'auxiliary'))
                       + ' <;> decide\n')
        out.append(nested + '· ')
    out.append('intro impossible; exact Fin.elim0 impossible\n' + indent + '· decide\n' + indent + '· decide\n')
    return _signature_audits(''.join(out))


def generate_block(export, parameter_root, role, chunk, export_hash):
    selected = select(export, parameter_root)
    return generate_selected_block(export,selected,role,chunk,export_hash)


def generate_selected_block(export, selected, role, chunk, export_hash, *, permutation_only=False):
    calls = [item for item in selected['calls'] if item['role'] == role]
    if len(calls) != 1:
        raise ValueError('missing/ambiguous hash block role')
    call = calls[0]
    segments = [item for item in call['segments'] if item['kind'] == 'round' and item['chunk'] == chunk]
    absorptions = [item for item in call['segments'] if item['kind'] == 'absorb']
    if [item['index'] for item in segments] != list(range(65)) or (not permutation_only and not 0 <= chunk < len(absorptions)):
        raise ValueError('incomplete or out-of-order permutation block')
    absorb = {'before':segments[0]['before'],'after':segments[0]['before'],'input_ids':[]} if permutation_only else absorptions[chunk]
    if absorb['after'] != segments[0]['before']:
        raise ValueError('absorption/permutation boundary mismatch')
    if any(left['after'] != right['before'] for left, right in zip(segments, segments[1:])):
        raise ValueError('round boundary mismatch')
    params, graph = call['parameters'], call['call']['graph']
    width, arity, domain = params['width'], graph['arity'], graph['domain']
    input_terms = {}
    for expected_id, source in zip(graph['inputs'], call['call']['inputs']):
        kind, terms = selected['observations'][source]
        if kind != 'linear':
            raise ValueError('unsupported nonlinear sponge input')
        input_terms[expected_id] = terms
    inputs = [input_terms[index] for index in absorb['input_ids']]
    all_inputs = [input_terms[index] for index in graph['inputs']]
    name = role.replace('.', '_') + f'_{chunk}'
    # Intern byte-identical LC lists only; this is not algebraic normalization.
    linear_definitions = {}

    def local_linear(terms):
        key = tuple(tuple(term) for term in terms)
        if key not in linear_definitions:
            linear_definitions[key] = f'lc_{len(linear_definitions)}'
        return linear_definitions[key]

    out = [f'''import ShielddSecurity.Poseidon
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace ShielddSecurity.RuntimeHashBlock_{name}
-- Exact export SHA256: {export_hash}
-- Full relation digest (extraction TCB): {export['relation_digest']}
-- One complete permutation/absorption block. Other blocks and source consumers
-- remain separate joins unless an explicit hash theorem below composes them.
def modulus : Nat := {P}
def rawRoundRows : Nat → List Row := fun index => match index with
''']
    if permutation_only:
        out[0] = out[0].replace(
            '-- One complete permutation/absorption block. Other blocks and source consumers\n'
            '-- remain separate joins unless an explicit hash theorem below composes them.\n',
            '-- One existing permutation only; states 0 are captured after absorption.\n'
            '-- Empty inputs/before bookkeeping does not describe runtime absorption.\n'
            '-- Absorption, other blocks, and hash consumers remain separate joins.\n')
    for index, segment in enumerate(segments):
        indices = sorted(set(segment['rows']) | {selected['constant_link']})
        out.append(f'  -- Original rows for round {index}: {indices}\n')
        rendered = ', '.join('⟨' + local_linear(selected['rows'][i][0]) + ', '
                             + local_linear(selected['rows'][i][1]) + '⟩' for i in indices)
        out.append(f'  | {index} => [{rendered}]\n')
    out.append(f'''  | _ => []
-- Repeated constant links denote the same original row. Local satisfaction is
-- derived from this common collected subset; it is not an extra theorem premise.
def rawRows : List Row := (List.range 65).flatMap rawRoundRows
def roundRows (index : Nat) : List Row := Compiler.unoutlineRows {selected['outline']} (rawRoundRows index)
def parameters : Poseidon.Parameters Int {width} where
  ark := fun index => match index with
''')
    for index, values in enumerate(params['ark']):
        out.append(f'    | {index} => ' + finite_function(values, lambda value: str(signed(value)), '0').replace('\n', '\n    ') + '\n')
    out.append('    | _ => fun _ => 0\n  mds := fun row => match row.val with\n')
    for index, values in enumerate(params['mds']):
        out.append(f'    | {index} => ' + finite_function(values, lambda value: str(signed(value)), '0').replace('\n', '\n    ') + '\n')
    out.append('    | _ => fun _ => 0\n')
    for name_state, table in [('states', [item['before'] for item in segments] + [segments[-1]['after']]),
                              ('shifted', [item['shifted'] for item in segments]),
                              ('transformed', [item['transformed'] for item in segments])]:
        out.append(f'def {name_state} : Nat → Poseidon.State Linear {width} := fun index => match index with\n')
        for index, values in enumerate(table):
            out.append(f'  | {index} => ' + finite_function(values, local_linear, '[]').replace('\n', '\n  ') + '\n')
        out.append('  | _ => fun _ => []\n')
    out.append(f'def before : Poseidon.State Linear {width} :=\n  '
               + finite_function(absorb['before'], local_linear, '[]').replace('\n', '\n  ') + '\n')
    out.append('def inputs : List Linear := [' + ', '.join(local_linear(terms) for terms in inputs) + ']\n')
    out.append('def callInputs : List Linear := [' + ', '.join(local_linear(terms) for terms in all_inputs) + ']\n')
    for index, segment in enumerate(segments):
        out.append(f'''
theorem constant_link_{index} : Compiler.checkRow modulus (rawRoundRows {index})
    ⟨[(0, 1), ({selected['outline']}, -1)], []⟩ = true := by decide

theorem certificate_{index} : Poseidon.RoundCertificate modulus (roundRows {index})
    parameters {index} (states {index}) (shifted {index})
      (transformed {index}) (states {index + 1}) := by
  ''')
        out.append(round_constructor(segment, width, '  ', local_linear))
    out.append(f'''
theorem constant_links : ∀ index : Fin 65, Compiler.checkRow modulus (rawRoundRows index.val)
    ⟨[(0, 1), ({selected['outline']}, -1)], []⟩ = true := by
  ''')
    for index in range(65):
        indent = '  ' + '  ' * index
        out.append('refine Fin.cases ?_ ?_\n' + indent + f'· exact constant_link_{index}\n' + indent + '· ')
    out.append('intro impossible; exact Fin.elim0 impossible\n')
    out.append('''
theorem certificates : ∀ index : Fin 65, Poseidon.RoundCertificate modulus (roundRows index.val)
    parameters index.val (states index.val) (shifted index.val)
      (transformed index.val) (states (index.val + 1)) := by
  ''')
    for index in range(65):
        indent = '  ' + '  ' * index
        out.append('refine Fin.cases ?_ ?_\n' + indent + '· ')
        out.append(f'exact certificate_{index}\n')
        out.append(indent + '· ')
    out.append('intro impossible; exact Fin.elim0 impossible\n')
    out.append(f'''
theorem permutation_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    (fun column => eval rho (states 65 column)) =
      Poseidon.permute (Poseidon.castParameters parameters) (fun column => eval rho (states 0 column)) := by
  have four : (4 : F) ≠ 0 := by
    intro zero
    have impossible : (4 : Nat) = 0 := bounded_cast_injective (F := F) (p := modulus)
      (by decide) (by decide) (by simpa using zero)
    omega
  apply Poseidon.rounds_chain (Poseidon.castParameters parameters)
    (fun index column => eval rho (states index column)) 65
  intro index bound
  have roundSatisfied : Satisfies rho (rawRoundRows index) := by
    intro row member
    exact satisfied row (List.mem_flatMap.mpr ⟨index, List.mem_range.mpr bound, member⟩)
  have normalized : Satisfies rho (roundRows index) :=
    Compiler.unoutline_rows_sound rho {selected['outline']} (rawRoundRows index) roundSatisfied (constant_links ⟨index, bound⟩)
  exact Poseidon.round_certificate_sound rho (roundRows index) parameters index
    (states index) (shifted index) (transformed index) (states (index + 1))
    one four normalized (certificates ⟨index, bound⟩)
''')
    if not permutation_only:
        out.append(f'''
theorem block_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    (fun column => eval rho (states 65 column)) =
      Poseidon.permute (Poseidon.castParameters parameters)
        (Poseidon.absorb (fun column => eval rho (before column)) (inputs.map (eval rho))) := by
  have absorption : ∀ column, Compiler.canonical modulus (states 0 column) =
      Compiler.canonical modulus (Poseidon.absorbLinear before inputs column) := by decide
  have boundary : (fun column => eval rho (states 0 column)) =
      Poseidon.absorb (fun column => eval rho (before column)) (inputs.map (eval rho)) := by
    calc
      _ = (fun column => eval rho (Poseidon.absorbLinear before inputs column)) := by
        funext column
        exact Compiler.canonical_equal rho _ _ (absorption column)
      _ = _ := Poseidon.eval_absorbLinear rho before inputs
  simpa only [boundary] using permutation_sound rho one satisfied

''')
    out.append('''#print axioms constant_links
#print axioms certificates
#print axioms permutation_sound
''')
    if not permutation_only:
        out.append('#print axioms block_sound\n')
    if not permutation_only and len(absorptions) == 1:
        if not (chunk == 0 and arity <= width - 1 and width in (3, 6)):
            raise ValueError('unsupported one-block hash shape')
        output_kind, output_terms = selected['observations'][call['call']['output']]
        if output_kind != 'linear' or output_terms != segments[-1]['after'][1]:
            raise ValueError('actual hash output coordinate mismatch')
        if width == 6:
            conclusion = f'''  have result := Poseidon.hash6_of_one_block (Poseidon.castParameters parameters) {domain}
    (callInputs.map (eval rho)) (fun column => eval rho (before column))
    (fun column => eval rho (states 65 column)) (by rfl)
    (by simpa only [callInputs, List.length_map, List.length_cons, List.length_nil] using initial_value)
    (block_sound rho one satisfied)
  change eval rho output = _ at result
  exact result
'''
        else:
            conclusion = f'''  have result := block_sound rho one satisfied
  rw [initial_value] at result
  have coordinate := congrArg (fun state : Poseidon.State F {width} => state ⟨1, by decide⟩) result
  change eval rho output = _ at coordinate
  simpa only [Poseidon.hash{width}, callInputs, inputs, List.map_cons, List.map_nil,
    List.length_cons, List.length_nil, Poseidon.chunks{width - 1}, Poseidon.sponge,
    List.foldl_cons, List.foldl_nil] using coordinate
'''
        out.append(f'''def output : Linear := {local_linear(output_terms)}
theorem actual_hash_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    eval rho output = Poseidon.hash{width} (Poseidon.castParameters parameters) {domain}
      (callInputs.map (eval rho)) := by
  have before_is_initial : before = Poseidon.initialLinear {domain} {arity} := by
    funext column
    exact (by decide : ∀ column : Fin {width}, before column = Poseidon.initialLinear {domain} {arity} column) column
  have initial_value : (fun column => eval rho (before column)) = Poseidon.initial {domain} {arity} := by
    simpa only [before_is_initial] using Poseidon.eval_initialLinear rho one {domain} {arity}
{conclusion}

#print axioms actual_hash_sound
''')
    out.append(f'end ShielddSecurity.RuntimeHashBlock_{name}\n')
    declarations = ''.join(f'def {identifier} : Linear := {linear(terms)}\n'
                           for terms, identifier in linear_definitions.items())
    return _signature_audits(''.join(out)).replace('def rawRoundRows', declarations + '\ndef rawRoundRows', 1)


def split_block(source, core_module):
    """Separate checked row certificates from final hash glue, without edits.

    The wrapper records the exact core bytes it imports. The execution receipt
    must check both source hashes; importing an error-recovery olean is forbidden.
    """
    if not core_module.isidentifier() or not core_module.isascii():
        raise ValueError('invalid generated core module name')
    marker = 'theorem actual_hash_sound'
    if source.count(marker) != 1:
        raise ValueError('split requires exactly one complete one-block hash')
    core, wrapper = source.split(marker)
    namespace = next(line for line in source.splitlines() if line.startswith('namespace '))
    ending = 'end ' + namespace.removeprefix('namespace ') + '\n'
    core += ending
    wrapper = (f'import ShielddSecurity.{core_module}\nset_option maxHeartbeats 4000000\nset_option maxRecDepth 4096\n'
               f'-- Exact generated core SHA256: {hashlib.sha256(core.encode()).hexdigest()}\n'
               + namespace + '\n' + marker + wrapper)
    return core, wrapper


def split_block_modules(source, prefix, rounds_per_module=5, *, linear_declarations_per_module=None):
    """Separate shared literal data, bounded round certificates, and symbolic glue.

    Each chunk imports the exact shared definitions, so no entire row table is
    duplicated. The final glue uses the existing symbolic rounds_chain lemma.
    All outputs are candidates until separately checked in dependency order.
    """
    if not prefix.isidentifier() or not prefix.isascii() or type(rounds_per_module) is not int or not 1 <= rounds_per_module <= 8:
        raise ValueError('invalid bounded hash module split')
    namespace = next(line for line in source.splitlines() if line.startswith('namespace '))
    ending = 'end '+namespace.removeprefix('namespace ')+'\n'
    if not source.endswith(ending) or source.count('theorem constant_link_0 :') != 1 or source.count('theorem constant_links :') != 1:
        raise ValueError('unsupported complete hash block source')
    head, rest = source.split('theorem constant_link_0 :',1)
    proof_text, glue = ('theorem constant_link_0 :'+rest).split('theorem constant_links :',1)
    matches = list(re.finditer(r'^theorem constant_link_(\d+) :',proof_text,re.MULTILINE))
    if [int(match[1]) for match in matches] != list(range(65)):
        raise ValueError('missing or reordered round certificates')
    blocks = [proof_text[match.start():matches[i+1].start() if i+1<len(matches) else len(proof_text)]
              for i,match in enumerate(matches)]
    data_name = prefix+'_Data'
    data = head+ending
    result = ([(data_name,data)] if linear_declarations_per_module is None else
              split_block_data(data,data_name,linear_declarations_per_module))
    data = result[-1][1]
    chunks = []
    for start in range(0,65,rounds_per_module):
        stop = min(start+rounds_per_module,65)
        name = prefix+f'_Rounds_{start}_{stop-1}'
        chunks.append(name)
        body = ''.join(blocks[start:stop])
        for index in range(start,stop):
            for theorem in (f'constant_link_{index}',f'certificate_{index}'):
                body += f'set_option pp.all true in\n#check @{theorem}\n#print axioms {theorem}\n'
        result.append((name,f'import ShielddSecurity.{data_name}\n'
            f'-- Exact shared data SHA256: {hashlib.sha256(data.encode()).hexdigest()}\n'
            'set_option maxHeartbeats 4000000\nset_option maxRecDepth 8192\n'+namespace+'\n'+body+ending))
    imports = ''.join(f'import ShielddSecurity.{name}\n' for name in chunks)
    result.append((prefix+'_Composition',imports+'set_option maxHeartbeats 4000000\n'
                   'set_option maxRecDepth 8192\n'+namespace+'\ntheorem constant_links :'+glue))
    return result


def split_block_data(source, data_module, declarations_per_module=32):
    """Partition literal LC declarations without changing any declaration bytes.

    This optional successor recipe addresses the measured wide Data elaboration
    heap. The final module keeps the original name/namespace and all row, state,
    and parameter declarations. No theorem or semantic check is moved or waived.
    A consumer must kernel-check every new dependency in the returned order.
    """
    if (not data_module.isidentifier() or not data_module.isascii() or
        type(declarations_per_module) is not int or not 1 <= declarations_per_module <= 64):
        raise ValueError('invalid bounded literal data split')
    namespaces = re.findall(r'^namespace ([A-Za-z0-9_.]+)$',source,re.MULTILINE)
    if len(namespaces)!=1 or re.search(r'^(?:theorem|#check|#print axioms)\b',source,re.MULTILINE):
        raise ValueError('literal split requires theorem-free single namespace data')
    namespace=namespaces[0];opening='namespace '+namespace+'\n';ending='end '+namespace+'\n'
    if not source.endswith(ending) or source.count('def rawRoundRows :')!=1:
        raise ValueError('literal split requires complete original block data')
    prefix,body=source.split(opening,1)
    declarations=list(re.finditer(r'^def lc_(\d+) : Linear := [^\n]*\n',body,re.MULTILINE))
    if not declarations or [int(match[1]) for match in declarations]!=list(range(len(declarations))):
        raise ValueError('literal data declarations missing or reordered')
    literal_start=declarations[0].start();literal_stop=declarations[-1].end()
    literals=body[literal_start:literal_stop]
    if literals!=''.join(match[0] for match in declarations):
        raise ValueError('literal declarations are not one contiguous exact block')
    parts=[];imports=''
    for start in range(0,len(declarations),declarations_per_module):
        stop=min(start+declarations_per_module,len(declarations))
        name=data_module+f'_Linear_{start}_{stop-1}'
        literal=''.join(match[0] for match in declarations[start:stop])
        parts.append((name,prefix+opening+literal+ending))
        imports+=f'import ShielddSecurity.{name}\n'
    # Original prefix supplies finite budgets and imports. Replacing only the
    # contiguous literal block preserves every subsequent definition exactly.
    parts.append((data_module,imports+prefix+opening+body[:literal_start]+body[literal_stop:]))
    return parts


def generate_glue_probe(export, parameter_root, role, chunk, export_hash):
    """Small actual boundary check, conditional on an explicit block equation.

    This never certifies rows. It tests the final script/data boundary before
    replaying the complete core, without importing a failed core artifact.
    """
    selected = select(export, parameter_root)
    calls = [item for item in selected['calls'] if item['role'] == role]
    if len(calls) != 1:
        raise ValueError('missing/ambiguous glue role')
    call = calls[0]
    absorbs = [item for item in call['segments'] if item['kind'] == 'absorb']
    rounds = [item for item in call['segments'] if item['kind'] == 'round']
    graph = call['call']['graph']
    if chunk != 0 or len(absorbs) != 1 or graph['width'] != 6:
        raise ValueError('glue probe supports one wide block only')
    inputs = [selected['observations'][identity][1] for identity in call['call']['inputs']]
    output = selected['observations'][call['call']['output']][1]
    domain, arity = graph['domain'], graph['arity']
    return f'''import ShielddSecurity.Poseidon
namespace ShielddSecurity.RuntimeHashGlueProbe
-- Exact export {export_hash}; conditional glue only, NOT a row certificate.
def before : Poseidon.State Linear 6 := {finite_function(absorbs[0]['before'], linear, '[]')}
def after : Poseidon.State Linear 6 := {finite_function(rounds[-1]['after'], linear, '[]')}
def inputs : List Linear := [{', '.join(map(linear, inputs))}]
def output : Linear := {linear(output)}
theorem conditional_glue {{F : Type}} [Field F] (parameters : Poseidon.Parameters F 6)
    (rho : Nat → F) (one : rho 0 = 1)
    (block : (fun column => eval rho (after column)) =
      Poseidon.permute parameters (Poseidon.absorb (fun column => eval rho (before column))
        (inputs.map (eval rho)))) :
    eval rho output = Poseidon.hash6 parameters {domain} (inputs.map (eval rho)) := by
  have before_is_initial : before = Poseidon.initialLinear {domain} {arity} := by
    funext column
    exact (by decide : ∀ column : Fin 6, before column = Poseidon.initialLinear {domain} {arity} column) column
  have initial_value : (fun column => eval rho (before column)) = Poseidon.initial {domain} {arity} := by
    simpa only [before_is_initial] using Poseidon.eval_initialLinear rho one {domain} {arity}
  have result := Poseidon.hash6_of_one_block parameters {domain} (inputs.map (eval rho))
    (fun column => eval rho (before column)) (fun column => eval rho (after column)) (by rfl)
    (by simpa only [inputs, List.length_map, List.length_cons, List.length_nil] using initial_value) block
  change eval rho output = _ at result
  exact result
#print axioms conditional_glue
end ShielddSecurity.RuntimeHashGlueProbe
'''


def generate_rnk_join(export, parameter_root, export_hash):
    """Compose the two actual RNK blocks; dependencies must be kernel checked."""
    selected = select(export, parameter_root)
    calls = [call for call in selected['calls'] if call['role'] == 'authorization.rnk']
    if len(calls) != 1:
        raise ValueError('missing/ambiguous RNK call')
    call = calls[0]
    graph = call['call']['graph']
    absorbs = [item for item in call['segments'] if item['kind'] == 'absorb']
    rounds = [[item for item in call['segments'] if item['kind'] == 'round'
               and item['chunk'] == chunk] for chunk in range(2)]
    if (graph['domain'] != 17 or graph['arity'] != 9 or call['parameters']['width'] != 6
            or len(absorbs) != 2 or any([item['index'] for item in block] != list(range(65))
                                       for block in rounds)):
        raise ValueError('unsupported RNK sponge shape')
    if (absorbs[0]['input_ids'] != graph['inputs'][:5]
            or absorbs[1]['input_ids'] != graph['inputs'][5:]
            or rounds[0][-1]['after'] != absorbs[1]['before']):
        raise ValueError('RNK partition/adjacent-block mismatch')
    kind, output = selected['observations'][call['call']['output']]
    if kind != 'linear' or output != rounds[1][-1]['after'][1]:
        raise ValueError('RNK output mismatch')
    source = f'''import ShielddSecurity.RuntimeHashRNK0
import ShielddSecurity.RuntimeHashRNK1
set_option maxHeartbeats 800000
namespace ShielddSecurity.RuntimeHashRNK
-- Exact export SHA256: {export_hash}
-- Full relation digest (extraction TCB): {export['relation_digest']}
-- Both imported blocks must be generated from this identical export.
def modulus : Nat := {P}
def rawRows : List Row := First.rawRows ++ Second.rawRows
def output : Linear := {linear(output)}

theorem actual_hash_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    eval rho output = Poseidon.hash6 (Poseidon.castParameters First.parameters) 17
      (First.callInputs.map (eval rho)) := by
  have first_rows : Satisfies rho First.rawRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inl member))
  have second_rows : Satisfies rho Second.rawRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inr member))
  have first := First.block_sound rho one first_rows
  have second := Second.block_sound rho one second_rows
  have parameters_equal : Second.parameters = First.parameters := rfl
  have initial_equal : First.before = Poseidon.initialLinear 17 9 := by
    funext column
    exact (by decide : ∀ column : Fin 6, First.before column = Poseidon.initialLinear 17 9 column) column
  have initial_value : (fun column => eval rho (First.before column)) = Poseidon.initial 17 9 := by
    simpa only [initial_equal] using Poseidon.eval_initialLinear rho one 17 9
  have adjacent : Second.before = First.states 65 := by
    funext column
    exact (by decide : ∀ column : Fin 6, Second.before column = First.states 65 column) column
  rw [initial_value] at first
  rw [parameters_equal, adjacent, first] at second
  have coordinate := congrArg (fun state : Poseidon.State F 6 => state ⟨1, by decide⟩) second
  change eval rho output = _ at coordinate
  simpa only [Poseidon.hash6, First.callInputs, First.inputs, Second.inputs,
    List.map_cons, List.map_nil, List.length_cons, List.length_nil,
    Poseidon.chunks5, Poseidon.sponge, List.foldl_cons, List.foldl_nil] using coordinate

#print axioms actual_hash_sound
end ShielddSecurity.RuntimeHashRNK
'''.replace('First.', 'RuntimeHashBlock_authorization_rnk_0.').replace(
        'Second.', 'RuntimeHashBlock_authorization_rnk_1.')
    return _signature_audits(source)


def generate_action_rk(export, parameter_root, export_hash):
    selected = select(export, parameter_root)
    links = selected['authorization_links']
    if [link['axis'] for link in links] != ['x', 'y']:
        raise ValueError('missing action key coordinate link')
    indices = sorted({selected['constant_link']} | {link['row'] for link in links})
    out = [f'''import ShielddSecurity.Compiler
set_option maxHeartbeats 200000
namespace ShielddSecurity.RuntimeActionKey
-- Actual export SHA256: {export_hash}
-- Full relation digest (extraction TCB): {export['relation_digest']}
-- Original row indices: {indices}
-- Wire coordinate equality only. Group computation, subgroup membership,
-- canonical serialization and actual signature verification remain separate.
def modulus : Nat := {P}
def rawRows : List Row := [
''']
    out.append(',\n'.join('  ⟨' + linear(selected['rows'][index][0]) + ', '
                         + linear(selected['rows'][index][1]) + '⟩' for index in indices))
    out.append(f''']
def rows : List Row := Compiler.unoutlineRows {selected['outline']} rawRows
''')
    for link in links:
        axis = link['axis']
        out.append(f'-- Same-constructor source handles {link["computed_source"]} and {link["statement_source"]}.\n')
        out.append(f'def computed_{axis} : Linear := {linear(link["computed"])}\n')
        out.append(f'def statement_{axis} : Linear := {linear(link["statement"])}\n')
    out.append(f'''
theorem action_key_coordinates_equal {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    eval rho computed_x = eval rho statement_x ∧
      eval rho computed_y = eval rho statement_y := by
  have normalized : Satisfies rho rows :=
    Compiler.unoutline_rows_sound rho {selected['outline']} rawRows satisfied (by decide)
  constructor
''')
    for link in links:
        axis = link['axis']
        left, right = f'computed_{axis}', f'statement_{axis}'
        if link['reversed']:
            left, right = right, left
        term = f'Compiler.checked_assertion_sound rho rows {left} {right} normalized (by decide)'
        out.append('  · exact ' + (f'({term}).symm' if link['reversed'] else term) + '\n')
    out.append('''
#print axioms action_key_coordinates_equal
end ShielddSecurity.RuntimeActionKey
''')
    return _signature_audits(''.join(out))


if __name__ == '__main__':
    if len(sys.argv) == 5 and sys.argv[3] in ('action-rk', 'rnk-join'):
        path, runtime, _, output = sys.argv[1:]
        mode = sys.argv[3]
    elif len(sys.argv) == 7 and sys.argv[3] in ('block', 'block-core', 'block-wrapper', 'block-glue'):
        path, runtime, _, role, chunk, output = sys.argv[1:]
        mode = sys.argv[3]
    else:
        path, runtime, role, chunk, index, output = sys.argv[1:]
        mode = 'round'
    raw = Path(path).read_bytes()
    export, parameters = decode_json(raw.decode('utf-8')), Path(runtime) / 'crates/crypto/primitives/params'
    digest = hashlib.sha256(raw).hexdigest()
    if mode == 'action-rk':
        result = generate_action_rk(export, parameters, digest)
    elif mode == 'rnk-join':
        result = generate_rnk_join(export, parameters, digest)
    elif mode == 'block-glue':
        result = generate_glue_probe(export, parameters, role, int(chunk), digest)
    elif mode in ('block', 'block-core', 'block-wrapper'):
        result = generate_block(export, parameters, role, int(chunk), digest)
        if mode != 'block':
            module = 'RuntimeHashBlock_' + role.replace('.', '_') + f'_{int(chunk)}_Core'
            core, wrapper = split_block(result, module)
            result = core if mode == 'block-core' else wrapper
            if mode == 'block-core' and Path(output).stem != module:
                raise ValueError('core filename must match generated import module')
    else:
        result = generate(export, parameters, role, int(chunk), int(index), digest)
    target = Path(output)
    temporary = target.with_suffix(target.suffix + '.tmp')
    temporary.write_text(result, encoding='utf-8')
    temporary.replace(target)
