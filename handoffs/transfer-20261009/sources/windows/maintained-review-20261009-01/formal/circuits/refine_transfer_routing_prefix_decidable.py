"""Preserve each physical prefix statement; simplify its dependent condition."""
import re

def generate(module,source):
    assert module=='RuntimeRoutingPrefixTheory' or re.fullmatch(r'RuntimeRoutingPrecision[01]Prefix',module)
    if module=='RuntimeRoutingPrefixTheory':return source
    before='  rw [present]\n'
    assert source.count(before)==1
    return source.replace(before,'  simp only [present]\n')
