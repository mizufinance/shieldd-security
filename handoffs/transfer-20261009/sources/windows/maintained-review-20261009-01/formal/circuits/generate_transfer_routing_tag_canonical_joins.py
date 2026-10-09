"""Generate four actual tag integer joins with the repaired common proof."""
from . import refine_transfer_routing_canonical_join as joins


def generate(extraction):
    assert extraction['schema'] == 'shieldd-transfer-routing-tag-rows-v1'
    result = {}
    families = set()
    for item in extraction['plan']['decompositions']:
        assert item['tag'] in ('route-bits', 'random-bits') and item['slot'] in (0, 1)
        family = ('Route' if item['tag'] == 'route-bits' else 'Random') + str(item['slot'])
        assert family not in families
        families.add(family)
        prefix = 'RuntimeRouting' + family + 'Canonical'
        derivative = dict(schema='shieldd-transfer-routing-row-derivative-v1',
                          selected_rows=extraction['selected_rows'],
                          plan=dict(permutation=item['plan'],
                                    constant_link=extraction['plan']['constant_link']))
        for name, text in joins.generate(derivative).items():
            fresh = name.replace('RuntimeRoutingCanonical', prefix)
            assert fresh not in result
            result[fresh] = text.replace('RuntimeRoutingCanonicalPage', prefix + 'Page').replace(
                'RuntimeRoutingCanonicalJoin', prefix + 'Join')
    assert families == {'Route0', 'Random0', 'Route1', 'Random1'} and len(result) == 4
    return result
