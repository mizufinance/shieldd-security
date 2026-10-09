"""Indexed finite-data checks for the same actual scalar chain certificates.

Retains the reviewed ordinary StepData view and all theorem conclusions. Dense
indices refer to the exact sorted original raw-row subset emitted by the base
generator. The indexed checker proves membership before reusing ordinary chain
soundness, and canonicalizes only the selected row instead of every shared row.
"""
import hashlib
from pathlib import Path
import sys

from generate_hash_round import linear, signed
from generate_scalar_chain import generate as generate_ordinary
from hash_rows import canonical, scaled
from poseidon_graph import P, decode_json
from scalar_rows import select


def indexed_product(certificate, positions):
    kind = certificate['kind']
    if kind == 'constant':
        constructor = 'foldedLeft' if certificate['side'] == 'left' else 'foldedRight'
        return f'.{constructor} ({signed(certificate["coefficient"])} : Int)'
    if kind == 'square':
        return f'.square {positions[certificate["rows"][0]]}'
    if kind == 'product':
        minus, plus = (positions[index] for index in certificate['rows'])
        return f'.product {minus} {plus} ' + linear(certificate['auxiliary'])
    raise ValueError('unsupported actual indexed scalar product')


def generate(export, parameter_root, export_hash, comparison=None):
    selected = select(export, parameter_root, comparison)
    source = generate_ordinary(export, parameter_root, export_hash, comparison)
    used = {selected['constant_link']}
    chosen = [step for step in selected['steps']
              if comparison is None or step['name'] == comparison]
    for step in chosen:
        used.update(step['certificate'].get('rows', []))
    positions = {original: dense for dense, original in enumerate(sorted(used))}
    # The base generator's rawRows/row order, all public definitions and theorem
    # conclusions remain unchanged. Only certificate data and their proof are
    # replaced by the indexed membership bridge in this atomic source producer.
    for name in ['quotient', 'remainder', 'last']:
        steps = [step for step in chosen if step['name'] == name]
        if not steps:
            continue
        records = []
        for step in steps:
            factor = (step['left'] if step['right'] else
                      canonical(((0, 1),) + scaled(step['left'], -1)))
            target = (canonical(step['after'] + step['left'] + ((0, P - 1),))
                      if step['right'] else step['after'])
            fields = [('before', linear(step['before'])), ('left', linear(step['left'])),
                      ('after', linear(step['after'])), ('right', 'true' if step['right'] else 'false'),
                      ('factor', linear(factor)), ('target', linear(target)),
                      ('product', indexed_product(step['certificate'], positions))]
            records.append('  { ' + ', '.join(f'{key} := {value}' for key, value in fields) + ' }')
        replacement = f'def {name}IndexedSteps : List ScalarIndexed.StepData := [\n'
        replacement += ',\n'.join(records) + '\n]\n'
        replacement += f'''def {name}Steps : List ScalarRows.StepData :=
  {name}IndexedSteps.map ScalarIndexed.StepData.ordinary
'''
        start_marker = f'def {name}Steps : List ScalarRows.StepData := ['
        end_marker = f'def {name}Final : Linear :='
        if source.count(start_marker) != 1 or source.count(end_marker) != 1:
            raise ValueError('reviewed base scalar generator shape changed')
        start = source.index(start_marker)
        end = source.index(end_marker, start)
        source = source[:start] + replacement + source[end:]
        old_proof = f'''theorem {name}_certificate : ScalarRows.checkChain modulus rows [(0, 1)] {name}Steps = true := by
  decide
'''
        new_proof = f'''theorem {name}_certificate : ScalarRows.checkChain modulus rows [(0, 1)] {name}Steps = true := by
  have indexed : ScalarIndexed.checkChain modulus rows [(0, 1)] {name}IndexedSteps = true := by
    decide
  exact ScalarIndexed.checked_chain_membership modulus rows [(0, 1)] {name}IndexedSteps indexed
'''
        if source.count(old_proof) != 1:
            raise ValueError('reviewed base scalar certificate shape changed')
        source = source.replace(old_proof, new_proof, 1)
    return source.replace('import ShielddSecurity.ScalarRows\n',
                          'import ShielddSecurity.ScalarIndexed\n', 1)


if __name__ == '__main__':
    arguments = sys.argv[1:]
    comparison = None
    if len(arguments) == 5 and arguments[0] == '--comparison':
        comparison, arguments = arguments[1], arguments[2:]
    path, runtime, output = arguments
    raw = Path(path).read_bytes()
    result = generate(decode_json(raw.decode('utf-8')),
                      Path(runtime) / 'crates/crypto/primitives/params',
                      hashlib.sha256(raw).hexdigest(), comparison)
    target = Path(output)
    temporary = target.with_suffix(target.suffix + '.tmp')
    temporary.write_text(result, encoding='utf-8')
    temporary.replace(target)
