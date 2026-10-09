"""Bound the actual255-bit routing comparator by16-step physical pages."""
from .generate_transfer_routing_zero_rows import _lc, _row
from .generate_hash_round import signed


def _ints(terms):
    return [[column, signed(int(value, 16) if isinstance(value, str) else value)]
            for column, value in terms]


def generate(extraction):
    assert extraction['schema'] == 'shieldd-transfer-routing-row-derivative-v1'
    plan = extraction['plan']['permutation']
    assert len(plan['steps']) == len(plan['columns']) == 255
    raw = {row['row']: row for row in extraction['selected_rows']}
    result = {}
    for number, start in enumerate(range(0, 255, 16)):
        steps = plan['steps'][start:start+16]
        name = f'RuntimeRoutingCanonicalPage{number:02}'
        indices = []
        expected = []
        descriptions = []
        for index, step in enumerate(steps, start):
            assert step['left'] == [[plan['columns'][index], 1]]
            assert step['right'] in [0, 1]
            indices.append(step['boolean_row'])
            expected.append(_row(step['left'], step['left']))
            cert = step['certificate']
            before, factor, product = map(_ints, [step['before'], step['factor'], step['product']])
            if cert.get('kind') == 'folded':
                assert index == 0 and before == [[0, 1]] and not cert['rows']
                data = '.foldedLeft 1'
            else:
                assert len(cert['rows']) == 2
                indices.extend(cert['rows'])
                auxiliary = _ints(cert['auxiliary'])
                expected.extend([
                    _row(before+[[c, -v] for c, v in factor], auxiliary),
                    _row(before+factor, auxiliary+[[c, 4*v] for c, v in product])])
                data = '(.product ' + _lc(auxiliary) + ')'
            descriptions.append('⟨' + ','.join([
                _lc(step['before']), _lc(step['left']), _lc(step['after']),
                'true' if step['right'] else 'false', _lc(step['factor']),
                _lc(step['product']), data]) + '⟩')
        indices.append(extraction['plan']['constant_link'])
        assert len(indices) == len(set(indices))
        source = ('import ShielddSecurity.RowOrientationSoundness\n'
                  'import ShielddSecurity.ScalarComparisonBounds\n'
                  'set_option maxHeartbeats 2000000\nset_option maxRecDepth 4096\n'
                  f'namespace ShielddSecurity.{name}\n')
        source += 'def physicalIndices : List Nat := ' + str(indices) + '\n'
        source += 'def rawRows : List Row := [\n' + ',\n'.join(_row(raw[i]['a'], raw[i]['b']) for i in indices) + ']\n'
        source += 'def expectedRows : List Row := [\n' + ',\n'.join(expected) + ']\n'
        source += 'def steps : List ScalarRows.StepData := [\n' + ',\n'.join(descriptions) + ']\n'
        source += 'def initial : Linear := ' + _lc(steps[0]['before']) + '\n'
        source += 'def final : Linear := ' + _lc(steps[-1]['after']) + '\n'
        source += '''theorem rows_sound {F : Type} [Field F] [CharP F Scalar.modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) : Satisfies rho expectedRows := by
  have actual := Compiler.unoutline_rows_sound rho 200692 rawRows satisfied (by decide)
  exact RowOrientationSoundness.checked_rows rho (Compiler.unoutlineRows 200692 rawRows)
    expectedRows (by decide) actual
theorem bits_checked : ScalarBits.checkBits Scalar.modulus expectedRows
    (steps.map ScalarRows.StepData.left) = true := by decide
theorem chain_checked : ScalarRows.checkChain Scalar.modulus expectedRows initial steps = true := by decide
theorem endpoint_checked : ScalarComparisonBounds.endpoint initial steps = final := by decide
'''
        for export in ['rows_sound', 'bits_checked', 'chain_checked', 'endpoint_checked']:
            source += f'set_option pp.all true in\n#check @{export}\n#print axioms {export}\n'
        result[name] = source + f'end ShielddSecurity.{name}\n'
    assert len(result) == 16
    return result
