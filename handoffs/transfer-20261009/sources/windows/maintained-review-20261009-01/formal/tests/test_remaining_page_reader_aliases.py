import hashlib,json,tempfile,unittest
from pathlib import Path
from integration import remaining_page_reader_aliases as aliases

class RemainingReaderAliasesTests(unittest.TestCase):
    def fixture(self,root):
        prefixes=[root/'original-first',root/'original-repeat']
        pages=[json.dumps({'ordinal':n,'ordinary_full_ordered_rows_equal':False}).encode() for n in range(2)]
        manifest=dict(schema='shieldd-transfer-remaining-source-pages-v1',scope='audit-sender',qualification=False,
            ordinary_full_ordered_rows_equal=False,repeated_observations_equal=False,
            pages=[dict(ordinal=n,suffix=f'pending-page-{n:03d}.json',bytes=len(raw),blake3='a'*64)
                for n,raw in enumerate(pages)])
        for prefix in prefixes:
            Path(str(prefix)+'.pending.json').write_bytes(json.dumps(manifest).encode())
            Path(str(prefix)+'.shape.json').write_bytes(b'{"full_rows":1}\n')
            Path(str(prefix)+'.rows').write_bytes(b'actual native spool fixture')
            for n,raw in enumerate(pages):Path(str(prefix)+f'.pending-page-{n:03d}.json').write_bytes(raw)
        return prefixes
    def test_preserves_original_false_bytes_and_spool_identity(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder);first,repeat=self.fixture(root);out=root/'aliases'
            before=Path(str(first)+'.pending.json').read_bytes()
            result=aliases.alias(first,repeat,out,'audit-sender');aliases.audit(out)
            self.assertEqual(Path(result[0]+'.pending.json').read_bytes(),before)
            self.assertFalse(json.loads(before)['qualification'])
            self.assertTrue(Path(result[0]+'.rows').samefile(Path(str(first)+'.rows')))
            self.assertEqual(Path(result[0]+'.page1.pending.json').read_bytes(),Path(str(first)+'.pending-page-001.json').read_bytes())
            Path(result[0]+'.page1.pending.json').write_bytes(b'changed')
            with self.assertRaises(ValueError):aliases.audit(out)
    def test_refuses_dropped_changed_qualified_or_reordered_originals_before_output(self):
        for edit in ['drop','changed','qualified','reordered']:
            with self.subTest(edit=edit),tempfile.TemporaryDirectory() as folder:
                root=Path(folder);first,repeat=self.fixture(root);out=root/'aliases'
                if edit=='drop':Path(str(first)+'.pending-page-001.json').unlink()
                elif edit=='changed':Path(str(repeat)+'.pending-page-001.json').write_bytes(b'changed')
                else:
                    for prefix in (first,repeat):
                        path=Path(str(prefix)+'.pending.json');obj=json.loads(path.read_bytes())
                        if edit=='qualified':obj['ordinary_full_ordered_rows_equal']=True
                        else:obj['pages'].reverse()
                        path.write_bytes(json.dumps(obj).encode())
                with self.assertRaises((ValueError,FileNotFoundError)):aliases.alias(first,repeat,out,'audit-sender')
                self.assertFalse(out.exists())
