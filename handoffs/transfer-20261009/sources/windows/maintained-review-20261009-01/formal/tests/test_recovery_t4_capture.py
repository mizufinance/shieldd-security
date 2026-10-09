"""Small source-only mode preservation and exact future74 refusal checks."""
from pathlib import Path
import unittest
from integration import recovery_t4_capture as recovery,transfer_t4_capture as retained


class RecoveryT4CaptureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        resources=Path('integration/observers')
        cls.catalogue=retained.catalogue((resources/'note_t4_pages_catalogue.rs').read_bytes(),
                                       (resources/'transfer_t4_hash_cones.rs').read_bytes())
        cls.export=retained.exporter((resources/'note_t4_pages_export.rs').read_bytes(),
                                    (resources/'transfer_t4_pages_serialization.rs').read_bytes())
        cls.cones=(resources/'recovery_hash_cones.rs').read_bytes()
        cls.roles=(resources/'recovery_capsule_roles.rs').read_bytes()
        cls.hashes=(resources/'recovery_hash_pages.rs').read_bytes()
        cls.qualifier=(resources/'recovery_t4_qualification.rs').read_bytes()

    def test_one_lowerer_retained65_prefix_then_eight_hashes_then_roles(self):
        result=recovery.catalogue(self.catalogue,self.cones)
        self.assertEqual(result.count(b'Relation::compile_inspected_pages'),1)
        self.assertIn(b'pages.len() == 65',result);self.assertIn(b'pages.len()==74',result)
        anchors=[b'pages.push(tree_selected);',b'for hash in &recovery_hashes {pages.push(',b'pages.push(recovery_selected);']
        self.assertEqual([result.index(a) for a in anchors],sorted(result.index(a) for a in anchors))
        self.assertIn(b'ordinal-65',result);self.assertIn(b'ordinal==73',result)
        self.assertIn(b'core.amount==output.note[1]',result);self.assertIn(b'core.blinding==output.note[0]',result)
        self.assertIn(b'let _capsule_capture = crate::recovery::capsule_inspection::begin()?;',result)
        for operation in (b'circuit::build(',b'Relation::compile_inspected_pages',b'let w = template(Family::Transfer);'):
            self.assertEqual(result.count(operation),self.catalogue.count(operation))
        with self.assertRaises(ValueError):recovery.catalogue(self.catalogue.replace(b'        65,',b'        66,'),self.cones)
        with self.assertRaises(ValueError):recovery.catalogue(result,self.cones)

    def test_new_exporter_mode_preserves_all_old_modes_and_ordinary_qualifier(self):
        base=retained.instrument_exporter(Path('integration/src/bin/transfer-ownership-inspection.rs').read_bytes(),self.export)
        fragment=recovery.exporter(self.export,self.roles,self.hashes)
        result=recovery.instrument_exporter(base,fragment,self.qualifier)
        self.assertIn(b'args[0]=="transfer-t4-recovery-pages-spool"',result)
        self.assertIn(b'args[0] == "transfer-t4-pages-spool"',result)
        self.assertEqual(result.count(b'compare_framed_rows(&paths[0], path, 200770, 262144)?;'),1)
        for name in (b'fn capture_transfer_t4_pages(',b'fn qualify_transfer_t4_pages(',b'fn transfer_t4_descriptor('):
            self.assertEqual(result.count(name),1)
        self.assertIn(b'count == 74 && copy == 200692',fragment)
        self.assertIn(b'"ordinary_full_ordered_rows_equal":false',fragment)
        self.assertIn(b'"repeated_observations_equal":false',fragment)
        self.assertNotIn(b'blake3::hash',fragment)
        with self.assertRaises(ValueError):recovery.instrument_exporter(result,fragment,self.qualifier)

    def test_qualification_retains_full65_check_and_exact_native_recovery_links(self):
        source=self.qualifier
        self.assertIn(b'pages.len()==74',source);self.assertIn(b'json!(&pages[..65])',source)
        self.assertIn(b'qualify_transfer_t4_pages(first,repeated,&retained)?;',source)
        self.assertIn(b'bytes==repeat && descriptor["blake3"]==packet_blake3(&bytes)',source)
        self.assertIn(b'c["amount"]==out["note"][1]',source)
        self.assertIn(b'c["blinding"]==out["note"][0]',source)
        self.assertIn(b'body["hash"]["inputs"]==inputs',source)
        self.assertIn(b'body["hash"]["output"]==output',source)
        self.assertIn(b'body["nodes"].as_array().map(|v|v.len()<=16384)',source)

    def test_identical_embedded_or_retained_qualifiers_are_preserved_once(self):
        base=retained.instrument_exporter(Path('integration/src/bin/transfer-ownership-inspection.rs').read_bytes(),self.export)
        fragment=recovery.exporter(self.export,self.roles,self.hashes)
        for parent,payload in ((base,fragment+self.qualifier),(base+b'\n'+self.qualifier,fragment),
            (base+b'\n'+self.qualifier,fragment+self.qualifier)):
            result=recovery.instrument_exporter(parent,payload,self.qualifier)
            for name in (b'recovery_t4_descriptor',b'qualify_recovery_t4_pages'):
                self.assertEqual(result.count(b'fn '+name+b'('),1)
            self.assertEqual(result.count(b'fn capture_transfer_t4_pages('),1)
        changed=self.qualifier.replace(b'pages.len()==74',b'pages.len()==75')
        with self.assertRaisesRegex(ValueError,'embedded.*drift'):
            recovery.instrument_exporter(base,fragment+changed,self.qualifier)
        with self.assertRaisesRegex(ValueError,'retained.*drift'):
            recovery.instrument_exporter(base+b'\n'+changed,fragment,self.qualifier)


if __name__=='__main__':unittest.main()
