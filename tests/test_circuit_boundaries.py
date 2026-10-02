"""Certificate parser negative cases; these are not runtime correspondence proofs."""
import copy
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'circuits'))
from generate import P
from volume_rows import select
from check import lean_environment, CheckError


def fixture():
    variables = list(range(3, 10))
    groups = [list(range(10+128*i, 138+128*i)) for i in range(6)]
    rows = []
    def row(a, b=()):
        def terms(xs):
            combined = {}
            for i, c in xs:
                combined[i] = (combined.get(i, 0)+c) % P
            return [[i, f'{c:064x}'] for i, c in sorted(combined.items()) if c]
        rows.append({'index': len(rows), 'a': terms(a), 'b': terms(b)})
    def weighted(bits, sign=1):
        return [(c, sign*2**i) for i, c in enumerate(bits)]
    for bits, values in zip(groups, [[(5,-1)],[(3,-1)],[(4,-1)],[(3,-1),(5,-1)],[(6,-1)],[(9,-1)]]):
        for c in bits:
            row([(c,1)],[(c,1)])
        row(weighted(bits)+values)
    row(weighted(groups[4])+weighted(groups[3],-1)+[(9,-1),(8,2**128)])
    row([(7,1)],[(7,1)])
    row([(8,1)],[(8,1)])
    for y, aux in [([(4,1),(3,-1),(5,-1)],778), ([(8,1)],780)]:
        row([(7,1)]+[(i,-c) for i,c in y],[(aux,1)])
        row([(7,1)]+y,[(aux,1),(aux+1,4)])
        row([(aux+1,1)])
    return {'subject':'actual Transfer amount/volume arithmetic row subset',
            'scalar_encoding':'canonical-big-endian-32', 'modulus_minus_one':f'{P-1:064x}',
            'domain_size':1024, 'variables':variables, 'bit_columns':groups,
            'row_count':len(rows), 'rows':rows}


class CertificateBoundaryTests(unittest.TestCase):
    def test_lean_discovery_rejects_wrong_versions_missing_imports_and_collisions(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            library = root / 'circuits/.lake/packages/mathlib/.lake/build/lib/lean'
            required = ['Mathlib/Algebra/Field/Basic', 'Mathlib/Tactic/Ring/RingNF', 'Mathlib/Algebra/CharP/Defs']
            for module in required:
                path = library / f'{module}.olean'
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(b'path-test-only')
            packages = [{'name': 'mathlib'}, {'name': 'unused'}]
            with patch('check.shutil.which', return_value='/pinned/bin/lean'), patch('check.run', return_value='Lean (version 4.30.0, release)') as version:
                result = lean_environment(packages, root)
                self.assertEqual(result['path'], str(library))
                version.return_value = 'Lean (version 4.30.0-rc1, release)'
                with self.assertRaisesRegex(CheckError, 'wrong Lean'):
                    lean_environment(packages, root)
                version.return_value = 'Lean (version 4.30.0, release)'
                duplicate = root / 'circuits/.lake/packages/unused/.lake/build/lib/lean/Mathlib/Algebra/Field/Basic.olean'
                duplicate.parent.mkdir(parents=True)
                duplicate.write_bytes(b'path-test-only')
                with self.assertRaisesRegex(CheckError, 'conflicting cached'):
                    lean_environment(packages, root)
                duplicate.unlink()
                (library / f'{required[0]}.olean').unlink()
                with self.assertRaisesRegex(CheckError, 'missing pinned Lean'):
                    lean_environment(packages, root)

    def test_volume_parser_rejects_invalid_original_coordinates(self):
        original = fixture()
        select(original)
        malformed = copy.deepcopy(original)
        malformed['rows'][0]['a'][0][0] = 1024
        with self.assertRaisesRegex(ValueError, 'row column'):
            select(malformed)
        malformed = copy.deepcopy(original)
        malformed['rows'][1]['index'] = 0
        with self.assertRaisesRegex(ValueError, 'contradictory original row'):
            select(malformed)
        malformed = copy.deepcopy(original)
        for row in malformed['rows']:
            for side in ['a','b']:
                for term in row[side]:
                    if term[0] == 778:
                        term[0] = 1
                row[side].sort()
        with self.assertRaisesRegex(ValueError, 'private product auxiliary'):
            select(malformed)
