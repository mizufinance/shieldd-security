"""Bind exact captured EPK row transports to the audited template row basis.

The caller first accepts the original strict captured-source recipe. This
adapter changes only the named scope-zero row definition used by a local
equality theorem; the target physical rows and transport map stay intact.
"""
import re
from . import transfer_relation as relation


def generate(name, source):
    match = re.fullmatch(r'RuntimeTransferEpk1RenamingRows(\d{3})', name)
    if match is None or not 16 <= int(match[1]) < 126:
        raise relation.RelationError('exact remaining scope-one window required')
    old = 'RuntimeTransferEpk0FixedWindow' + match[1]
    new = old + 'TemplateCompletion'
    expected_import = 'import ShielddSecurity.' + old + '\n'
    expected_basis = 'ShielddSecurity.' + old + '.rawRows.map '
    if (source.count(expected_import) != 1 or source.count(expected_basis) != 1
            or source.count(old) != 2):
        raise relation.RelationError('exact original import and physical row basis required')
    return name, source.replace(expected_import, 'import ShielddSecurity.' + new + '\n').replace(
        expected_basis, 'ShielddSecurity.' + new + '.rawRows.map ')
