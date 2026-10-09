"""Use the certified whole ownership trace as provider of window row data.

The trace imports the same window definitions and proves their whole native
construction. This changes direct imports only, preserving every definition,
theorem statement and proof body in each finite window adapter.
"""
import re


def generate(name, source):
    if not re.fullmatch(r'RuntimeRnkSparseBlock\d{3}', name):
        return source
    source, count = re.subn(r'^import ShielddSecurity\.RuntimeOwnershipWindow\d{3}$',
                            'import ShielddSecurity.RuntimeOwnershipConstructorTrace', source, flags=re.M)
    assert count in [0, 1]
    return source
