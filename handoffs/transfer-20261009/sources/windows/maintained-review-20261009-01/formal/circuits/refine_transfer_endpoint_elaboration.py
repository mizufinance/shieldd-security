"""Repair finite-list simplification and let-bound seed equalities.

Apply to the checked endpoint source. Only proof bodies change; the captured
rows, constructors, public statements and audit commands are preserved.
"""
import re


def generate(source):
    old = 'simp only [targetColumns,List.mem_cons,List.mem_singleton] at member'
    assert source.count(old) == 3
    source = source.replace(old, 'simp only [targetColumns,List.mem_cons,List.not_mem_nil,or_false] at member')
    old = 'simp only [endpointRows,List.mem_cons,List.mem_singleton] at member'
    assert source.count(old) == 1
    source = source.replace(old, 'simp only [endpointRows,List.mem_cons,List.not_mem_nil,or_false] at member')
    for backend, count in [('backend', 3), ('reader', 1)]:
        old = (f'    rw [seed_preserves fq fr model upstream {backend} sender scalar base 200692 (by decide),\n'
               f'      seed_preserves fq fr model upstream {backend} sender scalar base 0 (by decide),linked]')
        new = (f'    exact (seed_preserves fq fr model upstream {backend} sender scalar base 200692 (by decide)).trans\n'
               f'      (linked.trans (seed_preserves fq fr model upstream {backend} sender scalar base 0 (by decide)).symm)')
        assert source.count(old) == count
        source = source.replace(old, new)
    assert len(re.findall(r'^#check @', source, re.M)) == 8
    return source
