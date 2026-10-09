"""Reuse the finite canonical page generator for four captured tag inputs."""
from . import generate_transfer_routing_canonical_pages as pages
from . import generate_transfer_routing_canonical_join as joins


def generate(extraction):
    assert extraction['schema'] == 'shieldd-transfer-routing-tag-rows-v1'
    result = {}
    for item in extraction['plan']['decompositions']:
        family = 'Route' if item['tag'] == 'route-bits' else 'Random'
        prefix = f'RuntimeRouting{family}{item["slot"]}Canonical'
        derivative = dict(schema='shieldd-transfer-routing-row-derivative-v1',
                          selected_rows=extraction['selected_rows'],
                          plan=dict(permutation=item['plan'], constant_link=extraction['plan']['constant_link']))
        for name, text in {**pages.generate(derivative), **joins.generate(derivative)}.items():
            fresh = name.replace('RuntimeRoutingCanonical', prefix)
            assert fresh not in result
            result[fresh] = text.replace('RuntimeRoutingCanonicalPage', prefix+'Page').replace(
                'RuntimeRoutingCanonicalJoin', prefix+'Join')
    assert len(result) == 68
    return result
