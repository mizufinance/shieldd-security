import json
from pathlib import Path
import tempfile
import unittest
from circuits import generate_native_poseidon_parameters as producer


class NativePoseidonParameterTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        self.paths=[]
        for width,name in ((6,'poseidon381-wide.json'),(3,'poseidon381.json')):
            values=[[producer.P-1 if (r+c)%2 else r+c for c in range(width)] for r in range(65)]
            obj={'schema':'shieldd.poseidon381.v1','modulus':str(producer.P),'alpha':5,
                 'full_rounds':8,'partial_rounds':57,'skip_matrices':0,
                 'ark':[[f'{n:064x}' for n in row] for row in values],
                 'mds':[[f'{n:064x}' for n in row] for row in values[:width]],'vectors':[]}
            (self.root/name).write_text(json.dumps(obj))
        for i,namespace in enumerate(producer.NAMES):
            params=producer._checked(self.root/('poseidon381-wide.json' if i<2 else 'poseidon381.json'),6 if i<2 else 3)
            path=self.root/f'Data{i}.lean'
            path.write_text(f'namespace ShielddSecurity.{namespace}\n'+producer._table('parameters',params,'Int')+'def states := 0\n')
            self.paths.append(path)

    def test_signed_entries_and_native_loader_are_explicit(self):
        out=producer.generate(self.root,self.paths)
        self.assertEqual(out['coefficient_count'],630)
        self.assertEqual(len(out['audits']),12)
        self.assertIn('Represents (wideSigned.ark r.val c)',out['source'])
        self.assertIn('sourceBuffer (smallCanonical.mds r c)',out['source'])
        self.assertIn('wide_second_parameters',out['source'])
        self.assertNotIn('namespace P :=',out['source'])
        self.assertIn('local instance finiteEntriesDecidable',out['source'])
        self.assertIn('Fintype.decidableForallFintype',out['source'])
        self.assertNotIn('classical',out['source'])
        self.assertNotIn('native_decide',out['source'])

    def test_changed_actual_coefficient_rejected(self):
        self.paths[0].write_text(self.paths[0].read_text().replace('| 0 => 0','| 0 => 1',1))
        with self.assertRaisesRegex(ValueError,'coefficient table mismatch'):
            producer.generate(self.root,self.paths)

    def test_wrong_namespace_rejected(self):
        self.paths[1].write_text(self.paths[1].read_text().replace(producer.NAMES[1],producer.NAMES[0]))
        with self.assertRaisesRegex(ValueError,'namespace'):
            producer.generate(self.root,self.paths)

    def test_changed_sdk_entry_rejected(self):
        path=self.root/'poseidon381.json'
        obj=json.loads(path.read_text());obj['ark'][0][0]=f'{17:064x}';path.write_text(json.dumps(obj))
        with self.assertRaisesRegex(ValueError,'coefficient table mismatch'):
            producer.generate(self.root,self.paths)

    def test_noncanonical_sdk_and_recipe_rejected(self):
        path=self.root/'poseidon381.json'
        original=json.loads(path.read_text())
        for bad in (f'{producer.P:064x}','AA'*32):
            obj=json.loads(json.dumps(original));obj['ark'][0][0]=bad;path.write_text(json.dumps(obj))
            with self.assertRaises(ValueError):producer.generate(self.root,self.paths)
        original['alpha']=5.0;path.write_text(json.dumps(original))
        with self.assertRaisesRegex(ValueError,'noninteger'):
            producer.generate(self.root,self.paths)


if __name__=='__main__':unittest.main()
