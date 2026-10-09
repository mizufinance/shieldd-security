"""Render one bounded actual-row Boolean flag proof, without kernel credit.

The complete replay/capture/source identity and volume meaning are separate
joins. Generated checks refer to actual row bytes, not observer witness values.
"""
from . import transfer_relation as relation
from .transfer_encryption_dh_boolean import flag_plan, attach_rows
from .transfer_balance_rows import canonical, combine
from .generate_hash_round import linear, _signature_audits


def generate(checked, extracted):
    metadata = checked['metadata']
    if (checked.get('qualified') is not True or metadata.get('schema') != 'shieldd-transfer-encryption-dh-v1'
            or type(metadata.get('role')) is not int or metadata['role'] not in range(5)):
        raise relation.RelationError('DH Boolean renderer qualified occurrence required')
    identity = extracted.get('identity', {})
    if any(identity.get(a) != metadata[b] for a, b in
           [('relation_digest', 'relation_digest'), ('domain_size', 'domain_size'), ('stored_rows', 'full_rows')]):
        raise relation.RelationError('DH Boolean renderer exact ordinary identity required')
    plan = attach_rows(flag_plan(checked), extracted)
    if plan != extracted.get('flag_boolean') or len(plan['steps']) > 128:
        raise relation.RelationError('DH Boolean renderer exact bounded derivation plan required')
    raw = {}
    previous = -1
    selected = extracted.get('selected_rows')
    if not isinstance(selected, list) or not 0 < len(selected) <= 8192:
        raise relation.RelationError('DH Boolean renderer selected row bound')
    for item in selected:
        if not isinstance(item, dict) or set(item) != {'row', 'a', 'b'}:
            raise relation.RelationError('DH Boolean renderer row shape')
        index = relation.natural(item['row'], metadata['full_rows'])
        if index <= previous:
            raise relation.RelationError('DH Boolean renderer row order')
        previous = index
        for axis in ('a', 'b'):
            relation.terms(item[axis], metadata['domain_size'])
        raw[index] = tuple(tuple((c, int(v, 16)) for c, v in item[axis]) for axis in ('a', 'b'))
    copy = metadata['constant_copy']
    link = (canonical([(0, 1), (copy, -1)]), ())
    link_rows = [index for index, item in raw.items() if item == link]
    if not link_rows:
        raise relation.RelationError('DH Boolean renderer actual constant link required')
    indices = {min(link_rows)} | {row for step in plan['steps'] for row in step['rows']}
    if not indices <= set(raw) or len(indices) > 256:
        raise relation.RelationError('DH Boolean renderer actual obligation row coverage')
    normalized = {index: tuple(canonical((0 if c == copy else c, v) for c, v in terms)
                               for terms in row) for index, row in raw.items()}
    def matches(index, a, b):
        actual_a, actual_b = normalized[index]
        return actual_b == b and actual_a in (a, canonical((c, -v) for c, v in a))
    for step in plan['steps']:
        if step['kind'] == 'assert':
            if not matches(step['rows'][0], step['terms'], step['terms']):
                raise relation.RelationError('DH Boolean renderer actual Boolean row mismatch')
        elif step['kind'] == 'and':
            a, b = (checked['derived'][source] for source in step['inputs'])
            if len(step['rows']) == 1:
                valid = a == b and matches(step['rows'][0], a, step['terms'])
            elif len(step['rows']) == 2:
                first, second = step['rows']
                aux = normalized[first][1]
                valid = (matches(first, combine(a, b, -1), aux) and
                         matches(second, combine(a, b), combine(aux, step['terms'], 4)))
            else:
                valid = False
            if not valid:
                raise relation.RelationError('DH Boolean renderer actual product row mismatch')
    role = metadata['role']
    name = f'RuntimeTransferEncryptionDh{role}Flag'
    output = ['import ShielddSecurity.EncryptionDhBoolean\n',
              f'namespace ShielddSecurity.{name}\nset_option maxHeartbeats 400000\nset_option maxRecDepth 4096\n',
              f'def modulus : Nat := {relation.MODULUS}\n',
              f'def originalRows : List Nat := {sorted(indices)}\n',
              'def rawRows : List Row := [' + ',\n'.join('⟨' + linear(raw[i][0]) + ',' + linear(raw[i][1]) + '⟩'
                                                       for i in sorted(indices)) + ']\n',
              f'def unoutlined : List Row := Compiler.unoutlineRows {copy} rawRows\n',
              'def rows : List Row := unoutlined ++ unoutlined.map (fun row => ⟨scaleLinear (-1) row.a, row.b⟩)\n',
              f'theorem link_checked : Compiler.checkRow modulus rawRows ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide\n',
              'theorem rows_checked : rows.all (fun row => Compiler.checkRow modulus unoutlined row ||\n'
              '    Compiler.checkRow modulus unoutlined ⟨scaleLinear (-1) row.a,row.b⟩) = true := by decide\n',
              'theorem rows_satisfied {F : Type} [Field F] [CharP F modulus]\n'
              '    (rho : Nat → F) (satisfied : Satisfies rho rawRows) : Satisfies rho rows := by\n'
              f'  have original := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied link_checked\n'
              '  exact RowOrientationSoundness.checked_rows rho unoutlined rows rows_checked original\n']
    names = {step['source']: f'value{i}' for i, step in enumerate(plan['steps'])}
    for step in plan['steps']:
        output.append(f'def {names[step["source"]]} : Linear := {linear(step["terms"])}\n')
    flag = names[plan['root']] if plan['root'] is not None else linear(canonical([(0, plan['native'])]))
    output.append(f'def flag : Linear := {flag}\n')
    output.append('theorem flag_boolean {F : Type} [Field F] [CharP F modulus]\n'
                  '    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)\n'
                  '    (satisfied : Satisfies rho rawRows) : eval rho flag = 0 ∨ eval rho flag = 1 := by\n')
    if not plan['steps']:
        output.append('  simp [flag, eval, one]\n')
    else:
        output.append('  have actual := rows_satisfied rho satisfied\n')
        for step in plan['steps']:
            value = names[step['source']]
            proof = f'boolean_{value}'
            output.append(f'  have {proof} : eval rho {value} = 0 ∨ eval rho {value} = 1 := by\n')
            if step['kind'] == 'constant':
                output.append(f'    simp [{value}, eval, one]\n')
            elif step['kind'] == 'assert':
                output.append(f'    exact EncryptionDhBoolean.asserted rho rows {value} (by decide) actual\n')
            elif step['kind'] == 'alias':
                child = names[step['inputs'][0]]
                output.append(f'    simpa only [{value}, {child}] using boolean_{child}\n')
            elif step['kind'] == 'not':
                child = names[step['inputs'][0]]
                output.append(f'    apply EncryptionDhBoolean.negation (eval rho {child}) (eval rho {value}) boolean_{child}\n'
                              f'    have expression := Compiler.canonical_equal (p := modulus) rho {value} '
                              f'(Compiler.subtract [(0,1)] {child}) (by decide)\n'
                              '    simpa only [Compiler.eval_subtract, eval, Int.cast_one, one, one_mul, add_zero] using expression\n')
            elif step['kind'] == 'and':
                left, right = (names[source] for source in step['inputs'])
                output.append(f'    apply EncryptionDhBoolean.conjunction (eval rho {left}) (eval rho {right}) '
                              f'(eval rho {value}) boolean_{left} boolean_{right}\n')
                if len(step['rows']) == 1:
                    output.append(f'    have product := Compiler.checked_square_sound rho rows {left} {value} actual (by decide)\n'
                                  f'    simpa only [{left}, {right}] using product\n')
                elif len(step['rows']) == 2:
                    aux = canonical((0 if c == copy else c, v) for c, v in raw[step['rows'][0]][1])
                    output.append(f'    exact Compiler.checked_product_sound rho rows {left} {right} {value} '
                                  f'{linear(aux)} four actual (by decide) (by decide)\n')
                else:
                    raise relation.RelationError('DH Boolean renderer bounded square/product certificate')
            else:
                raise relation.RelationError('DH Boolean renderer unknown rule')
        output.append(f'  exact boolean_{names[plan["root"]]}\n')
    for theorem in ('link_checked', 'rows_checked', 'rows_satisfied', 'flag_boolean'):
        output.append(f'#print axioms {theorem}\n')
    output.append(f'end ShielddSecurity.{name}\n')
    return name, _signature_audits(''.join(output))
