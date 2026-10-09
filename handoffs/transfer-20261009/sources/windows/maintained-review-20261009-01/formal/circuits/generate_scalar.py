"""Generate narrowly scoped actual-row scalar comparator proofs.

The local step is a development unit for the complete reduction recurrence,
not a reduction/ownership certificate. It consumes the strict actual exporter
selector and checks original rows in Lean; no native witness values are used.
"""
import hashlib
from pathlib import Path
import sys

from generate_hash_round import linear, signed
from hash_rows import canonical, scaled
from poseidon_graph import P, decode_json
from scalar_rows import select


def generate_step(export, parameter_root, comparison, index, export_hash):
    selected = select(export, parameter_root)
    matches = [step for step in selected['steps']
               if step['name'] == comparison and step['index'] == index]
    if len(matches) != 1:
        raise ValueError('missing/ambiguous scalar comparator step')
    step = matches[0]
    certificate = step['certificate']
    indices = sorted(set(certificate.get('rows', [])) | {selected['constant_link']})
    rows = [selected['rows'][i] for i in indices]
    factor = (canonical(((0, 1),) + scaled(step['left'], -1))
              if step['right'] == 0 else step['left'])
    target = (step['after'] if step['right'] == 0 else
              canonical(step['after'] + step['left'] + ((0, P - 1),)))
    out = [f'''import ShielddSecurity.Compiler
import ShielddSecurity.Scalar
set_option maxHeartbeats 500000
namespace ShielddSecurity.RuntimeScalarStep_{comparison}_{index}
-- Exact exported source/rows SHA256: {export_hash}
-- Full relation digest (extraction boundary): {export['relation_digest']}
-- Original row indices: {indices}
-- Local comparator equation only, not complete scalar reduction or ownership.
def modulus : Nat := {P}
def rawRows : List Row := [
''']
    out.append(',\n'.join('  ⟨' + linear(a) + ', ' + linear(b) + '⟩' for a, b in rows))
    out.append(f''']
def rows : List Row := Compiler.unoutlineRows {selected['outline']} rawRows
''')
    for name, terms in [('before', step['before']), ('left', step['left']),
                        ('after', step['after']), ('factor', factor), ('target', target)]:
        out.append(f'def {name} : Linear := {linear(terms)}\n')
    out.append('''
theorem actual_step_sound {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    eval rho after = Scalar.comparisonPolynomial (eval rho before) (eval rho left)
''')
    out.append(f'      ({step["right"]} : F) := by\n')
    out.append(f'''  have normalized : Satisfies rho rows :=
    Compiler.unoutline_rows_sound rho {selected['outline']} rawRows satisfied (by decide)
  have multiplication : eval rho target = eval rho before * eval rho factor := by
''')
    if certificate['kind'] == 'product':
        out.append('''    have four : (4 : F) ≠ 0 := by
      intro zero
      have impossible : (4 : Nat) = 0 := bounded_cast_injective (F := F) (p := modulus)
        (by decide) (by decide) (by simpa using zero)
      omega
    exact Compiler.checked_product_sound rho rows before factor target
''')
        out.append('      (' + linear(certificate['auxiliary']) + ') four normalized (by decide) (by decide)\n')
    elif certificate['kind'] == 'square':
        out.append('''    have same : eval rho factor = eval rho before :=
      Compiler.canonical_equal rho factor before (by decide)
    rw [same]
    exact Compiler.checked_square_sound rho rows before target normalized (by decide)
''')
    elif certificate['kind'] == 'constant':
        value = signed(certificate['coefficient'])
        constant, other = (('before', 'factor') if certificate['side'] == 'left'
                           else ('factor', 'before'))
        out.append(f'''    have fixed : eval rho {constant} = (({value} : Int) : F) := by
      simpa only [eval, one, mul_one, add_zero] using
        Compiler.canonical_equal rho {constant} [(0, ({value} : Int))] (by decide)
    have folded : eval rho target = (({value} : Int) : F) * eval rho {other} := by
      simpa only [eval_scale] using
        Compiler.canonical_equal rho target (scaleLinear ({value} : Int) {other}) (by decide)
    rw [fixed]
    simpa only [mul_comm] using folded
''')
    else:
        raise ValueError('unsupported scalar product certificate')
    if step['right'] == 0:
        out.append('''  have factorValue : eval rho factor = 1 - eval rho left := by
    have same := Compiler.canonical_equal rho factor ([(0, 1)] ++ scaleLinear (-1) left) (by decide)
    simpa [eval_append, eval_scale, eval, one, sub_eq_add_neg] using same
  have targetValue : eval rho target = eval rho after :=
    Compiler.canonical_equal rho target after (by decide)
  rw [factorValue, targetValue] at multiplication
  simpa [Scalar.comparisonPolynomial] using multiplication
''')
    else:
        out.append('''  have factorValue : eval rho factor = eval rho left :=
    Compiler.canonical_equal rho factor left (by decide)
  have targetValue : eval rho target = eval rho after + eval rho left - 1 := by
    have same := Compiler.canonical_equal rho target (after ++ left ++ [(0, -1)]) (by decide)
    simpa [eval_append, eval, one, sub_eq_add_neg, add_assoc] using same
  rw [factorValue, targetValue] at multiplication
  calc
    eval rho after = 1 - eval rho left + eval rho before * eval rho left := by
      calc
        _ = (eval rho after + eval rho left - 1) + 1 - eval rho left := by ring
        _ = _ := by rw [multiplication]; ring
    _ = Scalar.comparisonPolynomial (eval rho before) (eval rho left) 1 := by
      unfold Scalar.comparisonPolynomial
      ring
''')
    out.append(f'''\n#print axioms actual_step_sound
end ShielddSecurity.RuntimeScalarStep_{comparison}_{index}
''')
    return ''.join(out)


if __name__ == '__main__':
    path, runtime, comparison, index, output = sys.argv[1:]
    raw = Path(path).read_bytes()
    result = generate_step(decode_json(raw.decode('utf-8')),
                           Path(runtime) / 'crates/crypto/primitives/params',
                           comparison, int(index), hashlib.sha256(raw).hexdigest())
    target = Path(output)
    temporary = target.with_suffix(target.suffix + '.tmp')
    temporary.write_text(result, encoding='utf-8')
    temporary.replace(target)
