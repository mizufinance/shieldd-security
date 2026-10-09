"""Repair initial-LC identification and Boolean equality goal elaboration."""
from . import generate_transfer_routing_canonical_join as original


def generate(extraction):
    outputs = original.generate(extraction)
    assert len(outputs) == 1
    result = {}
    for name, source in outputs.items():
        before = '  simp only [RuntimeRoutingChainTheory.endpoint_append]\n'
        after = before + ('  have initial : ([(0,1)] : Linear) = '
                          'RuntimeRoutingCanonicalPage00.initial := by decide\n'
                          '  rw [initial]\n')
        assert source.count(before) == 1
        source = source.replace(before, after)
        before = '  apply Bool.or_eq_true.mpr\n'
        after = '  simp only [ScalarComparisonBounds.checkEquality,Bool.or_eq_true]\n'
        assert source.count(before) == 2
        result[name] = source.replace(before, after)
    return result
