"""Generate original-row arithmetic proofs for the actual cofactor constructor.

All source nodes are independently matched to the eleven intended formulas.
Local checked row lemmas avoid a wide unrolled constraint walk. This generator
does not itself assert subgroup membership or completeness: the separately
checked inverse/assertion rows and standard curve model must be composed.
"""
import hashlib
from pathlib import Path
import sys

try:
    from .generate_hash_round import linear, signed
    from .group_rows import D
    from .poseidon_graph import P, decode_json
except ImportError:
    from generate_hash_round import linear, signed
    from group_rows import D
    from poseidon_graph import P, decode_json


def generate(export, parameter_root, export_hash):
    from group_cones import select
    selected = select(export, parameter_root)
    return generate_checked(selected, export_hash, export['relation_digest'])


def expected_graph_formula(graph, inputs):
    """Render a bounded independent polynomial; the kernel checks its meaning."""
    if type(graph.get('arity')) is not int or graph['arity'] != len(inputs):
        raise ValueError('wrong group polynomial input count')
    nodes=graph.get('nodes')
    if not isinstance(nodes,list) or not 1 <= len(nodes) <= 256:
        raise ValueError('group polynomial node bound')
    values=[]
    for index,node in enumerate(nodes):
        if not isinstance(node,dict):raise ValueError('group polynomial node must be an object')
        kind=node.get('kind')
        if kind=='input' and set(node)=={'kind','slot'}:
            slot=node['slot']
            if type(slot) is not int or not 0 <= slot < len(inputs):raise ValueError('group polynomial input slot')
            value=f'(eval rho {inputs[slot]})'
        elif kind=='constant' and set(node)=={'kind','value'}:
            coefficient=node['value']
            if type(coefficient) is not int or not 0 <= coefficient < P:raise ValueError('group polynomial coefficient')
            value=f'(({signed(coefficient)} : Int) : F)'
        elif kind in ('add','mul') and set(node)=={'kind','left','right'}:
            left,right=node['left'],node['right']
            if any(type(child) is not int or not 0 <= child < index for child in (left,right)):
                raise ValueError('group polynomial topology')
            value=f'({values[left]} {"+" if kind=="add" else "*"} {values[right]})'
        else:raise ValueError('unsupported group polynomial node')
        if len(value)>65536:raise ValueError('group polynomial expression bound')
        values.append(value)
    output=graph.get('output')
    if set(graph)!={'arity','nodes','output'} or type(output) is not int or not 0 <= output < len(values):
        raise ValueError('group polynomial output')
    return values[output]


def generate_checked(selected, export_hash, relation_digest, namespace='RuntimeGroupCones', full_audits=False):
    out = [f'''import ShielddSecurity.GroupWindows
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeGroupCones
-- Exact exported source/rows SHA256: {export_hash}
-- Full relation digest (extraction boundary): {relation_digest}
-- Original row indices: {list(selected['rows'])}
-- Full arithmetic cones only; boundary, subgroup, ownership and completion
-- obligations are not theorem premises hidden in witness-generation code.
def modulus : Nat := {P}
def coefficientD : Int := {signed(D)}
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
    for cone in selected['cones']:
        prefix = cone['role'].replace('.', '_')
        names = {identity: f'{prefix}_{identity}' for identity in cone['ordered']}
        value_defs = []
        for identity in cone['ordered']:
            name = names[identity]
            node = cone['source'][identity]
            certificate = cone['certificates'][identity]
            out.append(f'\ndef {name} : Linear := {linear(selected["observations"][identity][1])}\n')
            if certificate['kind'] == 'input':
                meaning = f'eval rho {name}'
            elif certificate['kind'] == 'constant':
                meaning = f'(({signed(certificate["coefficient"])} : Int) : F)'
            else:
                operation = '+' if node['kind'] == 'add' else '*'
                meaning = f'{names[node["left"]]}Value rho {operation} {names[node["right"]]}Value rho'
            out.append(f'def {name}Value {{F : Type}} [Field F] (rho : Nat → F) : F := {meaning}\n')
            value_defs.append(name + 'Value')
            out.append(f'''
theorem {name}_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rows) : eval rho {name} = {name}Value rho := by
''')
            kind = certificate['kind']
            if kind == 'input':
                out.append('  rfl\n')
                continue
            if kind == 'constant':
                value = signed(certificate['coefficient'])
                out.append(f'''  have fixed := Compiler.canonical_equal rho {name} [(0, ({value} : Int))] (by decide)
  simpa [{name}Value, eval, one] using fixed
''')
                continue
            left, right = names[node['left']], names[node['right']]
            conclusion = f'eval rho {name} = eval rho {left} ' + ('+' if kind == 'add' else '*') + f' eval rho {right}'
            out.append(f'  have nodeValue : {conclusion} := by\n')
            if kind == 'add':
                out.append(f'    exact Compiler.checked_add_sound rho {left} {right} {name} (by decide)\n')
            elif kind == 'square':
                out.append(f'''    have same : eval rho {right} = eval rho {left} :=
      Compiler.canonical_equal rho {right} {left} (by decide)
    rw [same]
    exact Compiler.checked_square_sound rho rows {left} {name} satisfied (by decide)
''')
            elif kind == 'product':
                out.append(f'''    exact Compiler.checked_product_sound rho rows {left} {right} {name}
      ({linear(certificate['auxiliary'])}) four satisfied (by decide) (by decide)
''')
            elif kind.startswith('folded_'):
                value = signed(certificate['coefficient'])
                constant, other = (left, right) if kind == 'folded_left' else (right, left)
                out.append(f'''    have fixed : eval rho {constant} = (({value} : Int) : F) := by
      simpa only [eval, one, mul_one, add_zero] using
        Compiler.canonical_equal rho {constant} [(0, ({value} : Int))] (by decide)
    have folded : eval rho {name} = (({value} : Int) : F) * eval rho {other} := by
      simpa only [eval_scale] using
        Compiler.canonical_equal rho {name} (scaleLinear ({value} : Int) {other}) (by decide)
    rw [fixed]
    simpa only [mul_comm] using folded
''')
            else:
                raise ValueError('unsupported group certificate constructor')
            rewrites = ', '.join(f'{child}_sound rho one four satisfied'
                                 for child in dict.fromkeys((left, right)))
            out.append(f'''  rw [{rewrites}] at nodeValue
  exact nodeValue
''')
        inputs = [names[identity] for identity in cone['inputs']]
        if 'expected_graph' in cone:
            formula=expected_graph_formula(cone['expected_graph'],inputs)
        else:
            formula=None
        x, y = (f'eval rho {name}' for name in inputs[:2]) if formula is None else ('','')
        point = f'(⟨{x}, {y}⟩ : Group.Point F)'
        delta = f'Group.delta (coefficientD : F) {point} {point}'
        if formula is not None:
            pass
        elif cone['role'] == 'curve.left':
            formula = f'({y}) * ({y}) - ({x}) * ({x})'
        elif cone['role'] == 'curve.right':
            formula = f'1 + (coefficientD : F) * ({x}) * ({x}) * ({y}) * ({y})'
        elif cone['role'].endswith('.denominator'):
            formula = f'(1 + {delta}) * (1 - {delta})'
        elif cone['role'].endswith('.x'):
            formula = f'Group.cross {point} {point} * (1 - {delta}) * eval rho {inputs[2]}'
        else:
            formula = f'Group.diagonal {point} {point} * (1 + {delta}) * eval rho {inputs[2]}'
        output = names[cone['output']]
        out.append(f'''
theorem {prefix}_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    eval rho {output} = {formula} := by
  have normalized : Satisfies rho rows :=
    Compiler.unoutline_rows_sound rho {selected['outline']} rawRows satisfied constantLink
  have computed := {output}_sound rho one (fourNonzero (F := F)) normalized
  simp only [{', '.join(value_defs)}] at computed
''')
        if 'expected_graph' in cone:
            out.append(f'  rw [computed] <;> ring\n\n#print axioms {prefix}_sound\n')
            continue
        out.append('  rw [computed]\n')
        if 'expected_graph' not in cone and cone['role'] != 'curve.left':
            out.append('  simp only [coefficientD, Group.delta, Group.cross, Group.diagonal]\n')
        out.append(f'  ring\n\n#print axioms {prefix}_sound\n')
    out.append('''
#print axioms constantLink
#print axioms fourNonzero
end ShielddSecurity.RuntimeGroupCones
''')
    source = ''.join(out).replace('RuntimeGroupCones', namespace)
    if full_audits:
        from .generate_hash_round import _signature_audits
        source = _signature_audits(source)
        source = source.replace('Exact exported source/rows SHA256:', 'Extraction-input (metadata) SHA256:')
    return source


def generate_cofactor(export, parameter_root, export_hash):
    """Compose both original-row lanes in one assignment, with named contracts.

    The primitive group model/order premises are global, independently supplied
    facts. The specific witness's curve membership, three doubling equations,
    equality to ak, and nonidentity are derived from raw-row satisfaction.
    """
    from generate_group import generate_boundaries
    from group_cones import select
    from scalar_rows import ORDER
    selected = select(export, parameter_root)
    boundary = generate_boundaries(export, parameter_root, export_hash)
    cones = generate(export, parameter_root, export_hash)
    out = ['import ShielddSecurity.GroupWindows\n',
           boundary.removeprefix('import ShielddSecurity.Compiler\n'),
           cones.removeprefix('import ShielddSecurity.GroupWindows\n'),
           f'''\nnamespace ShielddSecurity.RuntimeGroupCofactor
def subgroupOrder : Nat := {ORDER}
def rawRows : List Row := C.rawRows ++ B.rawRows
''']
    for role, terms in selected['roles'].items():
        out.append(f'def {role.replace(".", "_")} : Linear := {linear(terms)}\n')
    for name, role in [('preimage', 'preimage'), ('twice', 'double0.after'),
                       ('four', 'double1.after'), ('eight', 'double2.after'), ('point', 'point')]:
        out.append(f'''def {name} {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F :=
  ⟨eval rho {role.replace('.', '_')}_x, eval rho {role.replace('.', '_')}_y⟩
''')
    out.append('''
theorem actual_cofactor_sound {F J : Type} [Field F] [CharP F C.modulus] [AddCommGroup J]
    (model : Group.StandardCurveModel J (C.coefficientD : F))
    (standardOrder : ∀ represented : J, (8 * subgroupOrder) • represented = 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare (C.coefficientD : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    ∃ represented : J, model.coordinates represented = point rho ∧
      subgroupOrder • represented = 0 ∧ represented ≠ 0 := by
  have coneSatisfied : Satisfies rho C.rawRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inl member))
  have boundarySatisfied : Satisfies rho B.rawRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inr member))
  have curveLeft := C.curve_left_sound rho one coneSatisfied
  have curveRight := C.curve_right_sound rho one coneSatisfied
  change eval rho curve_left = _ at curveLeft
  change eval rho curve_right = _ at curveRight
  have curveEquality := B.curve_assertion_sound rho boundarySatisfied
  change eval rho curve_left = eval rho curve_right at curveEquality
  have valid : Group.OnCurve (C.coefficientD : F) (preimage rho) := by
    exact curveLeft.symm.trans (curveEquality.trans curveRight)
''')
    before_points, after_points = ['preimage', 'twice', 'four'], ['twice', 'four', 'eight']
    for index, (before, after) in enumerate(zip(before_points, after_points)):
        pfx = f'double{index}'
        out.append(f'''  have denominator{index} := C.{pfx}_denominator_sound rho one coneSatisfied
  change eval rho {pfx}_denominator =
    (1 + Group.delta (C.coefficientD : F) ({before} rho) ({before} rho)) *
      (1 - Group.delta (C.coefficientD : F) ({before} rho) ({before} rho)) at denominator{index}
  have boundaryInverse{index} := B.{pfx}_inverse_sound rho one boundarySatisfied
  have inverse{index} : eval rho {pfx}_denominator * eval rho {pfx}_inverse = 1 := by
    simpa only [B.{pfx}Left, B.{pfx}Right, {pfx}_denominator, {pfx}_inverse, mul_comm] using boundaryInverse{index}
  rw [denominator{index}] at inverse{index}
  have x{index} := C.{pfx}_after_x_sound rho one coneSatisfied
  have y{index} := C.{pfx}_after_y_sound rho one coneSatisfied
  have step{index} := Group.shared_inverse_double_sound (C.coefficientD : F) imaginary
    (eval rho {pfx}_inverse) nonSquare imaginarySquare ({before} rho) ({after} rho)
    {'valid' if index == 0 else f'step{index - 1}.2'} inverse{index} x{index} y{index}
''')
    out.append('''  have endpointX := B.cofactor_x_assertion_sound rho boundarySatisfied
  have endpointY := B.cofactor_y_assertion_sound rho boundarySatisfied
  have endpoint : eight rho = point rho := by
    change Group.Point.mk _ _ = Group.Point.mk _ _
    exact congrArg₂ Group.Point.mk endpointX endpointY
  obtain ⟨represented, coordinates, annihilated⟩ :=
    Group.cofactor_image_annihilated (C.coefficientD : F) model subgroupOrder standardOrder
      (preimage rho) (twice rho) (four rho) (eight rho) valid step0.1 step1.1 step2.1
  rw [endpoint] at coordinates
  have xNonzero := B.point_nonzero rho one boundarySatisfied
  have nonidentity : represented ≠ 0 := by
    apply Group.represented_nonidentity (C.coefficientD : F) model represented
    rw [coordinates]
    exact xNonzero
  exact ⟨represented, coordinates, annihilated, nonidentity⟩

#print axioms actual_cofactor_sound
end ShielddSecurity.RuntimeGroupCofactor
''')
    return ''.join(out).replace('B.', 'RuntimeGroupBoundary.').replace('C.', 'RuntimeGroupCones.')


if __name__ == '__main__':
    arguments = sys.argv[1:]
    combined = bool(arguments and arguments[0] == '--cofactor')
    if combined:
        arguments = arguments[1:]
    path, runtime, output = arguments
    raw = Path(path).read_bytes()
    result = (generate_cofactor if combined else generate)(decode_json(raw.decode('utf-8')),
                      Path(runtime) / 'crates/crypto/primitives/params',
                      hashlib.sha256(raw).hexdigest())
    target = Path(output)
    temporary = target.with_suffix(target.suffix + '.tmp')
    temporary.write_text(result, encoding='utf-8')
    temporary.replace(target)
