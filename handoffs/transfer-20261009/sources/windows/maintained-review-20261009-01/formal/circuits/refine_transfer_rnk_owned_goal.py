"""Expose the finite RNK ownership predicate before decidable elimination."""
import re


def generate(name, source):
    if not re.fullmatch(r'RuntimeRnkSparseBlock\d{3}', name):
        return source
    start = source.index('theorem writes_owned')
    end = source.index('\ntheorem row_supports', start)
    section = source[start:end]
    old = '  exact of_decide_eq_true (List.all_eq_true.mp checked column member)'
    assert section.count(old) == 1
    section = section.replace(old, '  change (2253 ≤ column ∧ column ≤ 3008) ∨ (51214 ≤ column ∧ column ≤ 55994)\n' + old)
    return source[:start] + section + source[end:]
