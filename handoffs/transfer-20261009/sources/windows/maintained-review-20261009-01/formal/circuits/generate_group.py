"""Generate actual cofactor boundary row equations, without subgroup claims.

The existing strict selector supplies original inverse and assertion rows.
Arithmetic-cone certificates, curve parameters and the standard group model
remain separate obligations. This generator never reads honest witness values.
"""
import hashlib
from pathlib import Path
import sys

from generate_hash_round import linear
from group_rows import select_boundary_rows
from hash_rows import canonical, scaled
from poseidon_graph import P, decode_json


def generate_boundaries(export, parameter_root, export_hash):
    selected = select_boundary_rows(export, parameter_root)
    roles = selected['roles']
    indices = sorted(selected['rows'])
    out = [f'''import ShielddSecurity.Compiler
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeGroupBoundary
-- Exact exported source/rows SHA256: {export_hash}
-- Full relation digest (extraction boundary): {export['relation_digest']}
-- Original row indices: {indices}
-- Boundary equations only: NOT curve, subgroup, ownership or signature proof.

def modulus : Nat := {P}
def rawRows : List Row := [
''']
    out.append(',\n'.join('  ⟨' + linear(a) + ', ' + linear(b) + '⟩'
                         for a, b in selected['rows'].values()))
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
    inverse_cases = [('point', selected['point_inverse'])]
    inverse_cases += [(f'double{i}', item) for i, item in enumerate(selected['double_inverses'])]
    point_x = canonical(roles['point.x'])
    if selected['point_inverse']['left'] == point_x:
        point_operand = 'pointLeft'
    elif selected['point_inverse']['right'] == point_x:
        point_operand = 'pointRight'
    else:
        raise ValueError('selected inverse does not constrain actual action key x')
    for name, item in inverse_cases:
        delta = canonical(item['output'] + scaled(item['target'], -1))
        if item['assertion']['expression'] == delta:
            assertion_proof = f'Compiler.checked_assertion_sound rho rows {name}Output [(0, 1)] normalized (by decide)'
        elif item['assertion']['expression'] == scaled(delta, -1):
            assertion_proof = f'(Compiler.checked_assertion_sound rho rows [(0, 1)] {name}Output normalized (by decide)).symm'
        else:
            raise ValueError('unsupported original inverse assertion orientation')
        out.append(f'''
def {name}Left : Linear := {linear(item['left'])}
def {name}Right : Linear := {linear(item['right'])}
def {name}Auxiliary : Linear := {linear(item['auxiliary'])}
def {name}Output : Linear := {linear(item['output'])}

theorem {name}_inverse_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    eval rho {name}Left * eval rho {name}Right = 1 := by
  have normalized : Satisfies rho rows :=
    Compiler.unoutline_rows_sound rho {selected['outline']} rawRows satisfied constantLink
  have multiplication := Compiler.checked_product_sound rho rows {name}Left {name}Right
    {name}Output {name}Auxiliary (fourNonzero (F := F)) normalized (by decide) (by decide)
  have asserted : eval rho {name}Output = 1 := by
    simpa [eval, one] using ({assertion_proof})
  rw [asserted] at multiplication
  exact multiplication.symm

#print axioms {name}_inverse_sound
''')
    equal_cases = [('curve', selected['curve_assertion'], roles['curve.left'], roles['curve.right'])]
    equal_cases += [(f'cofactor_{axis}', item, roles[f'double2.after.{axis}'], roles[f'point.{axis}'])
                    for axis, item in zip(('x', 'y'), selected['cofactor_assertions'])]
    for name, item, left, right in equal_cases:
        delta = canonical(left + scaled(right, -1))
        if item['expression'] == delta:
            first, second, reverse = name + 'Left', name + 'Right', ''
        elif item['expression'] == scaled(delta, -1):
            first, second, reverse = name + 'Right', name + 'Left', '.symm'
        else:
            raise ValueError('unknown group boundary assertion normalization')
        out.append(f'''
def {name}Left : Linear := {linear(left)}
def {name}Right : Linear := {linear(right)}

theorem {name}_assertion_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    eval rho {name}Left = eval rho {name}Right := by
  have normalized : Satisfies rho rows :=
    Compiler.unoutline_rows_sound rho {selected['outline']} rawRows satisfied constantLink
  exact (Compiler.checked_assertion_sound rho rows {first} {second} normalized (by decide)){reverse}

#print axioms {name}_assertion_sound
''')
    out.append(f'''
-- Nonidentity follows from an actual inverse relation, not a native constructor.
def pointX : Linear := {linear(roles['point.x'])}

theorem point_nonzero {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    eval rho pointX ≠ 0 := by
  intro zero
  have meaning : eval rho pointX = eval rho {point_operand} :=
    Compiler.canonical_equal rho pointX {point_operand} (by decide)
  rw [meaning] at zero
  have inverse := point_inverse_sound rho one satisfied
  simpa [zero] using inverse

#print axioms constantLink
#print axioms fourNonzero
#print axioms point_nonzero
end ShielddSecurity.RuntimeGroupBoundary
''')
    return ''.join(out)


if __name__ == '__main__':
    path, runtime, output = sys.argv[1:]
    raw = Path(path).read_bytes()
    result = generate_boundaries(decode_json(raw.decode('utf-8')),
                                 Path(runtime) / 'crates/crypto/primitives/params',
                                 hashlib.sha256(raw).hexdigest())
    target = Path(output)
    temporary = target.with_suffix(target.suffix + '.tmp')
    temporary.write_text(result, encoding='utf-8')
    temporary.replace(target)
