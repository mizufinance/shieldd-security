"""Elaborate the captured routing flag statements with decidable field equality.

The supplied equality decision is computational support, not an additional
algebraic restriction. The row premises and semantic conclusions are unchanged.
"""
from . import generate_transfer_routing_meaningful as original


def generate(extraction):
    outputs = original.generate(extraction)
    before = "variable {F : Type} [Field F] [CharP F Scalar.modulus]"
    after = "variable {F : Type} [Field F] [CharP F Scalar.modulus] [DecidableEq F]"
    assert len(outputs) == 1
    result = {}
    for name, source in outputs.items():
        assert source.count(before) == 1
        result[name] = source.replace(before, after)
    return result
