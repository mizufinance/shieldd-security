"""Prove each actual nested routing select equation under arbitrary row satisfaction."""
from .generate_transfer_routing_zero_rows import _lc, _row
from .transfer_fixed_spend import canonical, combine


def generate(extraction):
    assert extraction['schema'] == 'shieldd-transfer-routing-tag-rows-v1'
    raw = {row['row']: row for row in extraction['selected_rows']}
    result = {}
    for step in extraction['plan']['tag_steps']:
        slot, index = step['slot'], step['index']
        assert 0 <= slot < 2 and 0 <= index < 32
        name = f'RuntimeRoutingTagSelect{slot}Bit{index:02}'
        active, meaningful, route, random, public = map(canonical,
            [step[key] for key in ['active', 'meaningful', 'route', 'random', 'public']])
        inner, outer = step['inner'], step['outer']
        assert len(inner['rows']) == 2 and len(outer['rows']) == 3
        assert canonical(step['prefix']) == combine(random, canonical(inner['output']))
        expected = []
        for left, right, certificate in [
            (active, combine(route, random, -1), inner),
            (meaningful, canonical(inner['output']), outer)]:
            auxiliary, output = map(canonical, [certificate['auxiliary'], certificate['output']])
            expected.extend([_row(combine(left, right, -1), auxiliary),
                             _row(combine(left, right), combine(auxiliary, tuple((c, 4*v) for c, v in output)))])
        expected.extend([_row(combine(canonical(outer['output']), combine(public, random, -1), -1), ()),
                         _row(public, public)])
        indices = [*inner['rows'], *outer['rows'], step['public_boolean_row'], extraction['plan']['constant_link']]
        assert len(indices) == len(set(indices)) == 7
        source = ('import ShielddSecurity.RowOrientationSoundness\nimport ShielddSecurity.RoutingPrecision\n'
                  'set_option maxHeartbeats 2000000\nset_option maxRecDepth 4096\n'
                  f'namespace ShielddSecurity.{name}\n')
        source += 'def physicalIndices : List Nat := ' + str(indices) + '\n'
        source += 'def rawRows : List Row := [\n' + ',\n'.join(_row(raw[i]['a'], raw[i]['b']) for i in indices) + ']\n'
        source += 'def expectedRows : List Row := [\n' + ',\n'.join(expected) + ']\n'
        for field, terms in [('active', active), ('meaningful', meaningful), ('route', route),
                             ('random', random), ('public', public), ('innerOutput', inner['output']),
                             ('outerOutput', outer['output']), ('innerAux', inner['auxiliary']),
                             ('outerAux', outer['auxiliary'])]:
            source += f'def {field} : Linear := {_lc(terms)}\n'
        source += '''variable {F : Type} [Field F] [CharP F Scalar.modulus]
private theorem normalized (rho : Nat → F) (satisfied : Satisfies rho rawRows) : Satisfies rho expectedRows := by
  have actual := Compiler.unoutline_rows_sound rho 200692 rawRows satisfied (by decide)
  exact RowOrientationSoundness.checked_rows rho (Compiler.unoutlineRows 200692 rawRows)
    expectedRows (by decide) actual
theorem select_sound (rho : Nat → F) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    eval rho public = eval rho random + eval rho meaningful *
      (eval rho active * (eval rho route-eval rho random)) := by
  have rows := normalized rho satisfied
  have innerProduct := Compiler.checked_product_sound rho expectedRows active
    (Compiler.subtract route random) innerOutput innerAux four rows (by decide) (by decide)
  have outerProduct := Compiler.checked_product_sound rho expectedRows meaningful
    innerOutput outerOutput outerAux four rows (by decide) (by decide)
  have asserted := Compiler.checked_assertion_sound rho expectedRows outerOutput
    (Compiler.subtract public random) rows (by decide)
  rw [Compiler.eval_subtract] at asserted
  calc
    eval rho public = (eval rho public-eval rho random)+eval rho random := by ring
    _ = eval rho outerOutput+eval rho random := by rw [← asserted]
    _ = eval rho random + eval rho meaningful *
        (eval rho active * (eval rho route-eval rho random)) := by
      rw [outerProduct,innerProduct,Compiler.eval_subtract]
      ring
theorem public_boolean (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    Square (eval rho public) (eval rho public) := by
  exact Compiler.checked_row_sound rho expectedRows ⟨public,public⟩
    (normalized rho satisfied) (by decide)
'''
        for export in ['select_sound', 'public_boolean']:
            source += f'set_option pp.all true in\n#check @{export}\n#print axioms {export}\n'
        result[name] = source + f'end ShielddSecurity.{name}\n'
    assert len(result) == 64
    return result
