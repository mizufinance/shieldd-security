"""Strict actual LC/domain joins; map rows complete without desired u premise."""
import copy,io,re,tempfile,unittest
from pathlib import Path
from circuits import transfer_asset_hash as hashes, transfer_asset_map as maps
from circuits import transfer_asset_map_hash_join as join, transfer_relation as relation
from tests.test_transfer_asset_hash import fixture, encoded


class AssetMapHashJoinTests(unittest.TestCase):
    def test_exact_domain_asset_u_source_links_and_independent_native_success(self):
        page,map_data,caller,artifact,rows,_,_=fixture()
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder);(root/'poseidon381.json').write_bytes(encoded(artifact))
            selected=hashes.extract(page,io.BytesIO(rows),map_data,caller,root)
            mapped=maps.extract(map_data,io.BytesIO(rows),caller)
            result=join.plan(page,selected,map_data,mapped,caller,root)
            self.assertEqual(result['output'],result['mapped']['checked']['values']['u'])
            name,source=join.generate(page,selected,map_data,mapped,caller,root)
            self.assertEqual(name,'RuntimeTransferAssetMapHashJoin')
            checks=re.findall(r'#check @([A-Za-z0-9_]+)',source)
            self.assertEqual(len(checks),6)
            self.assertEqual(checks,re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
            self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
            self.assertIn('RuntimeTransferActualAssetHashCompletion.complete_hash',source)
            self.assertIn('RuntimeHashBlock_balance0_asset0_permutation0_0.parameters',source)
            self.assertIn('NativeTransferAdmission.balanceNative',source)
            self.assertIn('RuntimeTransferAssetMapLegalCompletion.complete_rows',source)
            # The actual kernel goal retained the abbrev head. Unfold that
            # owned assignment explicitly before applying kept-column facts.
            linked_proof=source.split('theorem hash_linked ',1)[1].split('theorem complete_map_inverse ',1)[0]
            copy_column=result['checked']['metadata']['constant_copy']
            self.assertIn(f'change RuntimeTransferActualAssetHashCompletion.completeAssignment rho {copy_column} = RuntimeTransferActualAssetHashCompletion.completeAssignment rho 0',linked_proof)
            self.assertLess(linked_proof.index('change '),linked_proof.index('  rw ['))
            statement=source[source.index('theorem complete_map_inverse'):].split(':= by',1)[0]
            for forbidden in ('(satisfied','(nativeInput','(nonidentity','(legal','(desired'):
                self.assertNotIn(forbidden,statement)
            self.assertIn('Hash row framing',source)
            changed=copy.deepcopy(selected);changed['selected_rows'].pop()
            with self.assertRaises(relation.RelationError):
                join.plan(page,changed,map_data,mapped,caller,root)
            with self.assertRaises(relation.RelationError):
                join.generate(page,selected,map_data,mapped,caller,root,hash_base='bad\nimport')


if __name__=='__main__':unittest.main()
