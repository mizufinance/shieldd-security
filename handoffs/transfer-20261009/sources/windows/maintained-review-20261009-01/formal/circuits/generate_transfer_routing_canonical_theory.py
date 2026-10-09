"""Compile existing symbolic comparator lemmas in a fresh owned namespace."""
from pathlib import Path


def generate():
    root = Path(__file__).resolve().parent / 'ShielddSecurity'
    composition = (root / 'ScalarChainComposition.lean').read_text()
    canonical = (root / 'RoutingPermutation.lean').read_text()
    assert composition.count('namespace ShielddSecurity.ScalarChainComposition') == 1
    assert canonical.count('namespace ShielddSecurity.RoutingPermutation') == 1
    composition = composition.replace('ShielddSecurity.ScalarChainComposition',
                                      'ShielddSecurity.RuntimeRoutingChainTheory')
    canonical = canonical.replace('ShielddSecurity.RoutingPermutation',
                                  'ShielddSecurity.RuntimeRoutingCanonicalTheory')
    return {'RuntimeRoutingChainTheory': composition,
            'RuntimeRoutingCanonicalTheory': canonical}
