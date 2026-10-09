"""Escape the existing prefix identifier, a Lean syntax keyword."""
import re


def generate(name, source):
    if name == 'RuntimeRoutingPrefixTheory':
        return source
    assert name in ['RuntimeRoutingPrecision0Prefix', 'RuntimeRoutingPrecision1Prefix']
    assert 'def prefix ' in source
    return re.sub(r'\bprefix\b', '«prefix»', source)
