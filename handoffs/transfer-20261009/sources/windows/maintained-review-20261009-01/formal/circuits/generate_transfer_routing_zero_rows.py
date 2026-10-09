"""One seven-row precision zero test per finite physical source module.

Every emitted semantic equation follows from the selected physical rows.
The checked constant-copy assertion supplies the unoutline transport; no
zero-selector, inverse equation or precision bound is assumed.
"""
from .generate_hash_round import linear
from .transfer_relation import MODULUS


def _lc(terms):
    return linear(tuple((c, int(v, 16) if isinstance(v, str) else v) for c, v in terms))


def _row(a, b):
    return '⟨' + _lc(a) + ',' + _lc(b) + '⟩'


def _subtract(a, b):
    return list(a) + [[c, -v] for c, v in b]


def generate(extraction):
    assert extraction['schema'] == 'shieldd-transfer-routing-row-derivative-v1'
    plan = extraction['plan']
    assert len(plan['precision']) == 2
    raw = {row['row']: row for row in extraction['selected_rows']}
    result = {}
    for slot, precision in enumerate(plan['precision']):
        assert [step['value'] for step in precision['steps']] == list(range(33))
        for step in precision['steps']:
            index = step['value']
            name = f'RuntimeRoutingZero{slot}Step{index:02}'
            denominator, flag, inverse = step['denominator'], step['zero'], step['inverse']
            ip, zp = step['inverse_product'], step['zero_product']
            indices = [step['boolean_row'], *ip['rows'], *zp['rows'], plan['constant_link']]
            assert len(indices) == len(set(indices)) == 8
            expected = [_row(flag, flag)]
            for right, product in [(inverse, ip), (flag, zp)]:
                expected += [_row(_subtract(denominator, right), product['auxiliary']),
                             _row(list(denominator) + list(right),
                                  list(product['auxiliary']) + [[c, 4*v] for c, v in product['output']])]
                target = [[0, 1]] + [[c, -v] for c, v in flag] if product is ip else []
                expected.append(_row(_subtract(product['output'], target), []))
            source = ('import ShielddSecurity.RowOrientationSoundness\n'
                      'import ShielddSecurity.RoutingPrecision\n'
                      'import ShielddSecurity.ScalarComparisonBounds\n'
                      'set_option maxHeartbeats 300000\nset_option maxRecDepth 4096\n'
                      f'namespace ShielddSecurity.{name}\n')
            source += f'def physicalIndices : List Nat := {indices}\n'
            source += 'def rawRows : List Row := [\n' + ',\n'.join(_row(raw[i]['a'], raw[i]['b']) for i in indices) + ']\n'
            source += 'def expectedRows : List Row := [\n' + ',\n'.join(expected) + ']\n'
            for label, terms in [('denominator', denominator), ('flag', flag), ('inverse', inverse),
                                 ('inverseOutput', ip['output']), ('zeroOutput', zp['output'])]:
                source += f'def {label} : Linear := {_lc(terms)}\n'
            source += '''variable {F : Type} [Field F] [CharP F Scalar.modulus]
private theorem normalized (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    Satisfies rho expectedRows := by
  have actual := Compiler.unoutline_rows_sound rho 200692 rawRows satisfied (by decide)
  exact RowOrientationSoundness.checked_rows rho (Compiler.unoutlineRows 200692 rawRows)
    expectedRows (by decide) actual
theorem inverse_sound (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    eval rho denominator * eval rho inverse = 1 - eval rho flag := by
  have rows := normalized rho satisfied
  have product := ScalarRows.checked_product_sound rho one four expectedRows rows
    denominator inverse inverseOutput (.product ''' + _lc(ip['auxiliary']) + ''') (by decide)
  have equation := ScalarComparisonBounds.checked_equality rho expectedRows rows
    inverseOutput ([(0,1)] ++ scaleLinear (-1) flag) (by decide)
  exact product.symm.trans (by simpa only [eval_append,eval_scale,eval,Int.cast_one,
    Int.cast_neg,one_mul,neg_one_mul,add_zero,one,sub_eq_add_neg] using equation)
theorem zero_sound (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) : eval rho denominator * eval rho flag = 0 := by
  have rows := normalized rho satisfied
  have product := ScalarRows.checked_product_sound rho one four expectedRows rows
    denominator flag zeroOutput (.product ''' + _lc(zp['auxiliary']) + ''') (by decide)
  have equation := ScalarComparisonBounds.checked_equality rho expectedRows rows zeroOutput [] (by decide)
  exact product.symm.trans equation
theorem flag_sound (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    eval rho flag = if eval rho denominator = 0 then 1 else 0 := by
  classical
  exact RoutingPrecision.zero_test_sound _ _ _ (inverse_sound rho one four satisfied)
    (zero_sound rho one four satisfied)
'''
            for export in ['inverse_sound', 'zero_sound', 'flag_sound']:
                source += f'set_option pp.all true in\n#check @{export}\n#print axioms {export}\n'
            result[name] = source + f'end ShielddSecurity.{name}\n'
    assert len(result) == 66
    return result
