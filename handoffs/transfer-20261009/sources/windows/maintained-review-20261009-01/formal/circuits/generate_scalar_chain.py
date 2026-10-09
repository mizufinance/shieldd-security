"""Instantiate all actual IVK comparator recurrences from original rows.

The strict selector checks original source steps, ordered bounds and roles.
The emitted symbolic chain derives every field prefix from arbitrary satisfying
assignments. Boolean/integer reconstruction, final guards and complete reduction
remain separate obligations; an honest Rust quotient is never a premise.
"""
import hashlib
from pathlib import Path
import sys

from generate_hash_round import linear, signed
from hash_rows import canonical, scaled
from poseidon_graph import P, decode_json
from scalar_rows import select


def product_data(certificate):
    kind = certificate['kind']
    if kind == 'constant':
        constructor = 'foldedLeft' if certificate['side'] == 'left' else 'foldedRight'
        return f'.{constructor} ({signed(certificate["coefficient"])} : Int)'
    if kind == 'square':
        return '.square'
    if kind == 'product':
        return '.product ' + linear(certificate['auxiliary'])
    raise ValueError('unknown actual scalar product shape')


def generate(export, parameter_root, export_hash, comparison=None):
    widths = {'quotient': 4, 'remainder': 252, 'last': 252}
    if comparison is not None and comparison not in widths:
        raise ValueError('unknown actual scalar comparison')
    selected = select(export, parameter_root, comparison)
    used = {selected['constant_link']}
    chosen = [step for step in selected['steps']
              if comparison is None or step['name'] == comparison]
    for step in chosen:
        used.update(step['certificate'].get('rows', []))
    out = [f'''import ShielddSecurity.ScalarRows
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeScalarChains
-- Exact exported source/rows SHA256: {export_hash}
-- Full relation digest (extraction boundary): {export['relation_digest']}
-- Original row indices: {sorted(used)}
-- Field comparator recurrences only; NOT canonical scalar reduction,
-- bit/integer completeness, ownership, or a full-family certificate.
def modulus : Nat := {P}
def rawRows : List Row := [
''']
    out.append(',\n'.join('  ⟨' + linear(selected['rows'][i][0]) + ', '
                         + linear(selected['rows'][i][1]) + '⟩' for i in sorted(used)))
    out.append(f''']
def rows : List Row := Compiler.unoutlineRows {selected['outline']} rawRows
theorem constantLink : Compiler.checkRow modulus rawRows
    ⟨[(0, 1), ({selected['outline']}, -1)], []⟩ = true := by decide
theorem fourNonzero {{F : Type}} [Field F] [CharP F modulus] : (4 : F) ≠ 0 := by
  intro zero
  have impossible : (4 : Nat) = 0 := bounded_cast_injective (F := F) (p := modulus)
    (by decide) (by decide) (by simpa using zero)
  omega
''')
    for name, width in widths.items():
        if comparison is not None and name != comparison:
            continue
        steps = [item for item in selected['steps'] if item['name'] == name]
        if [step['index'] for step in steps] != list(range(width)):
            raise ValueError('missing/out-of-order actual scalar comparator')
        out.append(f'\ndef {name}Steps : List ScalarRows.StepData := [\n')
        records = []
        for step in steps:
            factor = (step['left'] if step['right'] else
                      canonical(((0, 1),) + scaled(step['left'], -1)))
            target = (canonical(step['after'] + step['left'] + ((0, P - 1),))
                      if step['right'] else step['after'])
            values = [('before', linear(step['before'])), ('left', linear(step['left'])),
                      ('after', linear(step['after'])), ('right', 'true' if step['right'] else 'false'),
                      ('factor', linear(factor)), ('target', linear(target)),
                      ('product', product_data(step['certificate']))]
            records.append('  { ' + ', '.join(f'{key} := {value}' for key, value in values) + ' }')
        out.append(',\n'.join(records) + '\n]\n')
        out.append(f'def {name}Final : Linear := {linear(steps[-1]["after"])}\n')
        out.append(f'''
theorem {name}_certificate : ScalarRows.checkChain modulus rows [(0, 1)] {name}Steps = true := by
  decide

theorem {name}_actual_chain_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    eval rho {name}Final = ScalarRows.polynomialChain rho 1 {name}Steps := by
  have normalized : Satisfies rho rows :=
    Compiler.unoutline_rows_sound rho {selected['outline']} rawRows satisfied constantLink
  have recurrence := ScalarRows.checked_chain_sound rho one (fourNonzero (F := F))
    rows normalized [(0, 1)] {name}Steps {name}_certificate
  have endpoint : ScalarRows.evaluateChain rho [(0, 1)] {name}Steps = eval rho {name}Final := by
    rfl
  rw [endpoint] at recurrence
  simpa only [eval, one, mul_one, add_zero, Int.cast_one] using recurrence

#print axioms {name}_certificate
#print axioms {name}_actual_chain_sound
''')
    out.append('''
#print axioms constantLink
#print axioms fourNonzero
end ShielddSecurity.RuntimeScalarChains
''')
    return ''.join(out)


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
