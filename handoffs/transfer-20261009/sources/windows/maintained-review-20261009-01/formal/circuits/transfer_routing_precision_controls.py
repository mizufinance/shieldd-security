"""Finite execution controls for exact captured precision row polynomials.

These checks are Python field arithmetic on captured physical rows, not
Shieldd runtime execution, a universal proof, or full Transfer certification.
"""
from .transfer_relation import MODULUS


def _coefficient(value):
    return int(value, 16) if isinstance(value, str) else value


def _set_unit(assignment, linear, value):
    assert len(linear) == 1 and _coefficient(linear[0][1]) == 1
    column = linear[0][0]
    assert column not in assignment or assignment[column] == value % MODULUS
    assignment[column] = value % MODULUS


def _eval(assignment, linear):
    assert all(column in assignment for column, _ in linear)
    return sum(_coefficient(value)*assignment[column] for column, value in linear) % MODULUS


def _assignment(plan, precision, copy, wrong_flag=None):
    values = {0: 1, copy: 1}
    _set_unit(values, plan['input'], precision)
    for step in plan['steps']:
        difference = (precision-step['value']) % MODULUS
        inverse = pow(difference, -1, MODULUS) if difference else 0
        flag = int(difference == 0)
        if wrong_flag == step['value']:
            flag = 1-flag
        _set_unit(values, step['zero'], flag)
        _set_unit(values, step['inverse'], inverse)
        for right, product in [(inverse, step['inverse_product']), (flag, step['zero_product'])]:
            _set_unit(values, product['output'], difference*right)
            _set_unit(values, product['auxiliary'], (difference-right)**2)
    return values


def _failures(raw, indices, assignment):
    failures = []
    for index in indices:
        row = raw[index]
        residual = (_eval(assignment, row['a'])**2-_eval(assignment, row['b'])) % MODULUS
        if residual:
            failures.append(dict(physical_row=index, residual=f'{residual:064x}'))
    return failures


def check(extraction):
    assert extraction['schema'] == 'shieldd-transfer-routing-row-derivative-v1'
    raw = {row['row']: row for row in extraction['selected_rows']}
    copy = extraction['identity']['constant_copy'] if 'constant_copy' in extraction['identity'] else 200692
    # The captured copy index is also present explicitly in the actual copy row.
    copy_row = raw[extraction['plan']['constant_link']]
    columns = {c for c, _ in copy_row['a']}
    assert columns == {0, copy} and not copy_row['b']
    positive = 0
    controls = []
    for slot, plan in enumerate(extraction['plan']['precision']):
        assert [step['value'] for step in plan['steps']] == list(range(33))
        tests = []
        for step in plan['steps']:
            tests.extend([step['boolean_row'], *step['inverse_product']['rows'], *step['zero_product']['rows']])
        assert len(tests) == len(set(tests)) == 231
        indices = tests+[plan['onehot_row'], extraction['plan']['constant_link']]
        for precision in range(33):
            failures = _failures(raw, indices, _assignment(plan, precision, copy))
            assert not failures, (slot, precision, failures)
            positive += 1
        for precision in [33, MODULUS-1]:
            assignment = _assignment(plan, precision, copy)
            assert not _failures(raw, tests, assignment)
            failures = _failures(raw, indices, assignment)
            assert [failure['physical_row'] for failure in failures] == [plan['onehot_row']]
            controls.append(dict(control='outside precision domain', slot=slot,
                                 precision=str(precision), intended='separate physical onehot assertion fails',
                                 observed=failures))
        assignment = _assignment(plan, 0, copy, wrong_flag=0)
        failures = _failures(raw, indices, assignment)
        inverse_assertion = plan['steps'][0]['inverse_product']['rows'][-1]
        assert inverse_assertion in [failure['physical_row'] for failure in failures]
        assert set(failure['physical_row'] for failure in failures) == {inverse_assertion, plan['onehot_row']}
        controls.append(dict(control='wrong zero selector', slot=slot, precision='0',
                             intended='physical inverse-product target assertion fails', observed=failures))
    return dict(positive_assignments=positive, negative_controls=controls,
                evidence_kind='finite captured-row execution with Python field arithmetic',
                runtime_shieldd_execution=False, universal_proof=False, full_transfer_certification=False)
