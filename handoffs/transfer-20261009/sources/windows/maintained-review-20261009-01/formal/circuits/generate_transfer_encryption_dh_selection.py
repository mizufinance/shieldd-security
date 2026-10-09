"""Actual-row arithmetic for the outer and nested two-coordinate selectors.

Only a finite independently matched selector is rendered. Booleanity, input
key/subgroup/parameter meaning and full caller correspondence are separate.
"""
from . import transfer_relation as relation
from .transfer_arithmetic import normalize_selection, product_certificate
from .transfer_balance_rows import canonical, combine
from .transfer_encryption_dh_selection import match_selection
from .transfer_encryption_dh_keys import infer_regulated_selectors
from .generate_hash_round import linear, signed, _signature_audits


def _generate(checked, extracted, view, name):
    metadata = checked['metadata']
    if checked.get('qualified') is not True or metadata.get('schema') != 'shieldd-transfer-encryption-dh-v1':
        raise relation.RelationError('DH selector renderer qualified actual occurrence required')
    raw, normalized = normalize_selection(extracted, metadata, checked['metadata_sha256'])
    sym = dict(normalized)
    sym.update({-i - 1: (canonical((c, -v) for c, v in a), b) for i, (a, b) in normalized.items()})
    selection = match_selection(view)
    actual = lambda value: (checked['derived'][value[1]] if value[0] == 'source'
                            else canonical([(0, value[1])]))
    operands = [view['bindings']['flagged'], *view['bindings']['detection_key'], *view['bindings']['payload_key']]
    lcs = list(map(actual, operands))
    used = {min(i for i, row in raw.items() if row == (canonical([(0, 1), (metadata['constant_copy'], -1)]), ()))}
    plans = []
    for cone in selection['cones']:
        graph, terms, certificates = cone['graph'], [], []
        if len(graph['nodes']) > 32 or graph['arity'] == 0:
            raise relation.RelationError('DH selector bounded nonconstant graph required')
        matched = {}
        for index, source in cone['pairs']:
            handle = ('cwn'.index(source[0]), int(source[1:]))
            matched.setdefault(index, set()).add(checked['derived'][handle])
        for index, node in enumerate(graph['nodes']):
            kind = node['kind']
            certificate = dict(kind=kind)
            if kind == 'input':
                value = checked['derived'][cone['inputs'][node['slot']]]
            elif kind == 'constant':
                value = canonical([(0, node['value'])])
            elif kind == 'add':
                value = combine(terms[node['left']], terms[node['right']])
            elif kind == 'mul':
                left, right = terms[node['left']], terms[node['right']]
                folded = next(((side, lc, other) for side, lc, other in
                               [('left', left, right), ('right', right, left)]
                               if not lc or len(lc) == 1 and lc[0][0] == 0), None)
                if folded:
                    side, lc, other = folded
                    coefficient = lc[0][1] if lc else 0
                    value = canonical((c, v * coefficient) for c, v in other)
                else:
                    if len(matched.get(index, ())) != 1:
                        raise relation.RelationError('DH selector exact materialized product LC required')
                    value = next(iter(matched[index]))
                certificate = product_certificate(left, right, value, sym)
                used.update(i if i >= 0 else -i - 1 for i in certificate['rows'])
            else:
                raise relation.RelationError('DH selector unknown source operation')
            if any(value != lc for lc in matched.get(index, ())):
                raise relation.RelationError('DH selector observed LC disagrees with independent graph')
            terms.append(value)
            certificates.append(certificate)
        if terms[graph['output']] != actual(cone['output']):
            raise relation.RelationError('DH selector actual output LC mismatch')
        plans.append(dict(cone=cone, terms=terms, certificates=certificates))
    if len(used) > 128:
        raise relation.RelationError('DH selector original row128 bound')
    copy = metadata['constant_copy']
    output = [f'import ShielddSecurity.EncryptionDhSelection\nimport ShielddSecurity.RowOrientationSoundness\n',
              f'namespace ShielddSecurity.{name}\nset_option maxHeartbeats 400000\nset_option maxRecDepth 4096\n',
              f'def modulus : Nat := {relation.MODULUS}\n',
              f'def originalRows : List Nat := {sorted(used)}\n',
              'def rawRows : List Row := [' + ',\n'.join('⟨' + linear(raw[i][0]) + ',' + linear(raw[i][1]) + '⟩' for i in sorted(used)) + ']\n',
              f'def unoutlined : List Row := Compiler.unoutlineRows {copy} rawRows\n',
              'def rows : List Row := unoutlined ++ unoutlined.map (fun row => ⟨scaleLinear (-1) row.a,row.b⟩)\n',
              f'theorem link_checked : Compiler.checkRow modulus rawRows ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide\n',
              'theorem rows_checked : rows.all (fun row => Compiler.checkRow modulus unoutlined row ||\n'
              '    Compiler.checkRow modulus unoutlined ⟨scaleLinear (-1) row.a,row.b⟩) = true := by decide\n',
              'theorem rows_satisfied {F : Type} [Field F] [CharP F modulus]\n'
              '    (rho : Nat → F) (satisfied : Satisfies rho rawRows) : Satisfies rho rows := by\n'
              f'  have original := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied link_checked\n'
              '  exact RowOrientationSoundness.checked_rows rho unoutlined rows rows_checked original\n']
    for label, terms in zip(('flag', 'yesX', 'yesY', 'noX', 'noY'), lcs):
        output.append(f'def {label} : Linear := {linear(terms)}\n')
    for axis in (0, 1):
        output.append(f'def out{axis} : Linear := {linear(actual(view["points"]["base"][axis]))}\n')
    common = ('{F : Type} [Field F] [CharP F modulus] (rho : Nat → F)\n'
              '    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rows)')
    for axis, plan in enumerate(plans):
        cone, terms, certificates = plan['cone'], plan['terms'], plan['certificates']
        graph = cone['graph']
        semantics = []
        for index, node in enumerate(graph['nodes']):
            ref = f'a{axis}n{index}'
            meaning = f'a{axis}s{index}'
            output.append(f'def {ref} : Linear := {linear(terms[index])}\n')
            if node['kind'] == 'constant':
                expression = f'(({signed(node["value"])} : Int) : F)'
            elif node['kind'] == 'input':
                expression = f'eval rho {linear(checked["derived"][cone["inputs"][node["slot"]]])}'
            else:
                symbol = '+' if node['kind'] == 'add' else '*'
                expression = f'a{axis}s{node["left"]} rho {symbol} a{axis}s{node["right"]} rho'
            output.append(f'def {meaning} {{F : Type}} [Field F] (rho : Nat → F) : F := {expression}\n')
            semantics.append(meaning)
            output.append(f'private theorem {ref}_sound {common} : eval rho {ref} = {meaning} rho := by\n')
            kind, certificate = node['kind'], certificates[index]
            if kind == 'input':
                output.append('  rfl\n')
            elif kind == 'constant':
                output.append(f'  simp [{ref},{meaning},eval,one]\n')
            else:
                left, right = (f'a{axis}n{node[side]}' for side in ('left', 'right'))
                output.append(f'  dsimp only [{meaning}]\n'
                              f'  rw [← {left}_sound rho one four satisfied, ← {right}_sound rho one four satisfied]\n')
                if kind == 'add':
                    output.append(f'  exact Compiler.checked_add_sound (p := modulus) rho {left} {right} {ref} (by decide)\n')
                elif certificate['kind'] == 'product':
                    output.append(f'  exact Compiler.checked_product_sound rho rows {left} {right} {ref} '
                                  f'{linear(certificate["auxiliary"])} four satisfied (by decide) (by decide)\n')
                elif certificate['kind'] == 'square':
                    output.append(f'  simpa only [{left},{right}] using Compiler.checked_square_sound rho rows {left} {ref} satisfied (by decide)\n')
                elif certificate['kind'].startswith('folded_'):
                    side = certificate['kind'].split('_', 1)[1]
                    scalar, other = (left, right) if side == 'left' else (right, left)
                    value = signed(certificate['coefficient'])
                    output.append(f'  have scalar : eval rho {scalar} = (({value} : Int) : F) := by\n'
                                  f'    have same := Compiler.canonical_equal (p := modulus) rho {scalar} [(0,({value}:Int))] (by decide)\n'
                                  '    simpa only [eval,one,one_mul,mul_one,add_zero] using same\n'
                                  f'  have same := Compiler.canonical_equal (p := modulus) rho {ref} (scaleLinear ({value}) {other}) (by decide)\n'
                                  '  simpa only [eval_scale,scalar' +
                                  (']' if side == 'left' else ',mul_comm]') + ' using same\n')
                else:
                    raise relation.RelationError('DH selector unsupported arithmetic certificate')
        last = f'a{axis}n{graph["output"]}'
        yes, no = ('yesX', 'noX') if axis == 0 else ('yesY', 'noY')
        public = common.replace('satisfied : Satisfies rho rows', 'satisfied : Satisfies rho rawRows')
        output.append(f'theorem axis{axis}_interpolation {public} :\n'
                      f'    eval rho out{axis} = eval rho {no} + eval rho flag * (eval rho {yes} - eval rho {no}) := by\n'
                      '  have actual := rows_satisfied rho satisfied\n'
                      f'  have result := {last}_sound rho one four actual\n'
                      '  calc\n'
                      f'    eval rho out{axis} = a{axis}s{graph["output"]} rho := result\n'
                      f'    _ = _ := by simp only [{",".join(semantics)},{yes},{no},flag,eval,one]; ring\n')
    if selection['role'] == 0:
        for axis in (0, 1):
            output.append(f'theorem axis{axis}_interpolation {{F : Type}} [Field F] (rho : Nat → F) :\n'
                          f'    eval rho out{axis} = eval rho {"yesX" if axis == 0 else "yesY"} := rfl\n')
    exports = ['link_checked', 'rows_checked', 'rows_satisfied', 'axis0_interpolation', 'axis1_interpolation']
    output.extend(f'#print axioms {theorem}\n' for theorem in exports)
    output.append(f'end ShielddSecurity.{name}\n')
    return name, _signature_audits(''.join(output))


def generate(checked, extracted):
    role = checked['metadata']['role']
    if type(role) is not int or role not in range(5):
        raise relation.RelationError('DH selector exact five-role coverage')
    return _generate(checked, extracted, checked, f'RuntimeTransferEncryptionDh{role}Selection')


def generate_regulated(checked, extracted):
    inferred = infer_regulated_selectors(checked)
    result = []
    for key, label in [('detection_key', 'Detection'), ('payload_key', 'Payload')]:
        selector = inferred['selectors'][key]
        view = dict(checked, metadata=dict(checked['metadata'], role=1),
                    bindings=dict(flagged=selector['flag'], detection_key=selector['leaf'], payload_key=selector['fallback']),
                    points={'base': selector['output']})
        result.append(_generate(checked, extracted, view, f'RuntimeTransferEncryption{label}KeySelection'))
    return result
