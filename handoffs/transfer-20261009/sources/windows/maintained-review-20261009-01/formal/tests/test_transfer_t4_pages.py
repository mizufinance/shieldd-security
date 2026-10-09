"""Tiny manifest/typed capsule view controls; runtime qualification is separate."""
import copy,json,unittest
from blake3 import blake3
from circuits import transfer_t4_pages as pages,transfer_recovery_pages as recovery,transfer_relation as relation
from circuits.transfer_note_t4_pages import encoded
from tests.test_transfer_recovery_capsule import fixture


def manifest(owner,metadata,digests=None):
    identities={k:metadata[k] for k in pages.IDENTITY}
    count=len(owner.inventory());schema='shieldd-transfer-t4-pages-v1' if count==65 else 'shieldd-transfer-t4-recovery-pages-v1'
    return dict(schema=schema,family='transfer',scope=owner.SCOPE,**identities,
        ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True,
        pages=[dict(ordinal=i,slot=s,role=r,level=l,block=b,blake3=(digests or {}).get(i,'0'*64))
            for i,(s,r,l,b) in enumerate(owner.inventory())])


class T4PageTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.data,cls.output,cls.caller,_=fixture();cls.metadata=json.loads(cls.data)

    def test_exact_retained_prefix_roles_and_recovery_order(self):
        self.assertEqual(len(pages.inventory()),65);self.assertEqual(len(recovery.inventory()),74)
        self.assertEqual(recovery.inventory()[:65],pages.inventory())
        self.assertEqual(pages.inventory()[55:],[(0,'note',0,0),(0,'note',0,1),(0,'recovery',0,0),(0,'recovery',0,1),
            (1,'note',0,0),(1,'note',0,1),(1,'recovery',0,0),(1,'recovery',0,1),(0,'asset',0,0),(0,'roles',0,0)])
        self.assertEqual(recovery.inventory()[65:],[(s,r,0,0) for s in range(2) for r in ('secret','confirmation','amount-stream','blinding-stream')]+[(0,'recovery-roles',0,0)])
        for owner in (pages,recovery):
            original=manifest(owner,self.metadata)
            checked=owner.inspect_manifest(encoded(original),self.metadata['relation_digest'])
            self.assertEqual(checked,original)
            changes=[lambda m:m['pages'].pop(),lambda m:m['pages'].append(m['pages'][-1]),
                lambda m:m['pages'][55].update(role='recovery'),lambda m:m['pages'][0].update(slot=True),
                lambda m:m.update(repeated_observations_equal=False),lambda m:m.update(unowned=True),
                lambda m:m['pages'][-1].update(blake3='g'*64)]
            for mutate in changes:
                altered=copy.deepcopy(original);mutate(altered)
                with self.assertRaises(relation.RelationError):owner.inspect_manifest(encoded(altered),self.metadata['relation_digest'])

    def test_capsule_view_binds_original_pending_bytes_and_typed_output_sources(self):
        pending=copy.deepcopy(self.metadata);pending.update(ordinary_full_ordered_rows_equal=False,repeated_observations_equal=False)
        data=encoded(pending);packet=manifest(recovery,self.metadata,{73:blake3(data).hexdigest()})
        view,original_sha=recovery.qualified_roles(encoded(packet),data,self.output,self.caller)
        self.assertEqual(json.loads(view),self.metadata)
        self.assertEqual(json.loads(data),pending)
        import hashlib
        self.assertEqual(original_sha,hashlib.sha256(data).hexdigest())
        with self.assertRaisesRegex(relation.RelationError,'bytes/digest'):
            recovery.qualified_roles(encoded(packet),data+b' ',self.output,self.caller)
        altered=copy.deepcopy(pending);altered['capsules'][0]['amount']=altered['capsules'][1]['amount']
        altered_data=encoded(altered);packet['pages'][73]['blake3']=blake3(altered_data).hexdigest()
        with self.assertRaises(relation.RelationError):recovery.qualified_roles(encoded(packet),altered_data,self.output,self.caller)
        packet['pages'][73]['blake3']=blake3(self.data).hexdigest()
        with self.assertRaisesRegex(relation.RelationError,'pending'):
            recovery.qualified_roles(encoded(packet),self.data,self.output,self.caller)

    def test_page_role_bool_alias_and_missing_qualification_refuse(self):
        packet=manifest(pages,self.metadata)
        body=dict(**{k:self.metadata[k] for k in pages.IDENTITY},ordinary_full_ordered_rows_equal=False,
            repeated_observations_equal=False,slot=0,role='asset',level=0,block=0)
        data=encoded(body);packet['pages'][63]['blake3']=blake3(data).hexdigest()
        checked=pages.inspect_manifest(encoded(packet),self.metadata['relation_digest'])
        self.assertEqual(pages.pending_page(checked,data,63),body)
        body['slot']=False;data=encoded(body);packet['pages'][63]['blake3']=blake3(data).hexdigest()
        checked=pages.inspect_manifest(encoded(packet),self.metadata['relation_digest'])
        with self.assertRaises(relation.RelationError):pages.pending_page(checked,data,63)
        for ordinal in (55,63,64,73):
            with self.assertRaises(relation.RelationError):
                recovery.qualified_hash(encoded(manifest(recovery,self.metadata)),b'{}',ordinal,self.data,self.output,self.caller,None)

    def test_derived65_consumer_retains_actual74_schema_bytes_and_all_checks(self):
        original=manifest(recovery,self.metadata);data=encoded(original)
        receipt=recovery.qualified_prefix65_view(data,self.metadata['relation_digest'])
        self.assertEqual(receipt['parent_data'],data)
        self.assertEqual(receipt['parent_manifest'],original)
        self.assertEqual(receipt['parent_manifest']['schema'],'shieldd-transfer-t4-recovery-pages-v1')
        self.assertEqual(list(receipt['prefix_descriptors']),original['pages'][:65])
        self.assertEqual(pages.inspect_component_manifest(data,self.metadata['relation_digest']),original)
        self.assertTrue(receipt['ordinary_full_ordered_rows_equal'])
        for mutate in (lambda m:m.update(repeated_observations_equal=False),lambda m:m['pages'][72].update(role='secret'),
                       lambda m:m['pages'][64].update(role='tree'),lambda m:m['pages'].pop()):
            bad=copy.deepcopy(original);mutate(bad)
            with self.assertRaises(relation.RelationError):recovery.qualified_prefix65_view(encoded(bad),self.metadata['relation_digest'])
            with self.assertRaises(relation.RelationError):pages.inspect_component_manifest(encoded(bad),self.metadata['relation_digest'])


if __name__=='__main__':unittest.main()
