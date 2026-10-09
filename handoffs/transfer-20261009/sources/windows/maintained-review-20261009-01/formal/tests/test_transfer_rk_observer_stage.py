"""Fresh staging controls; never build or execute diagnostic Rust."""
import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from circuits import transfer_rk_observer_stage as staging
from circuits.transfer_relation import RelationError


class RkStageTests(unittest.TestCase):
    def source_roots(self,root):
        runtime,formal=root/'runtime',root/'formal'
        sources={
          runtime/'crates/crypto/circuits/src/group.rs':'pub mod fixed_inspection;\n',
          runtime/'crates/crypto/circuits/src/group/inspection.rs':'pub(crate) fn scope() -> Option<Scope> {\n}\n',
          runtime/'crates/crypto/circuits/src/note.rs':
            '    let rk = group::witness_subgroup(ctx, &w.rk, &w.rk.cofactor_preimage());\n    rk.assert_non_identity();\n',
          runtime/'crates/crypto/circuits/src/catalogue.rs':'// original catalogue\n',
          runtime/'crates/crypto/circuits/src/group/rk_inspection.rs':'// new selector\n',
          runtime/'crates/crypto/circuits/src/catalogue/rk_inspection.rs':'// new catalogue include\n',
          formal/'integration/src/bin/transfer-ownership-inspection.rs':
            '    let args: Vec<_> = std::env::args().skip(1).collect();\n        Some("shieldd-transfer-fixed-spend-v1") |\n',
          formal/'integration/src/inspection/transfer_rk_subgroup.rs':'// new exporter include\n'}
        for path,value in sources.items():path.parent.mkdir(parents=True,exist_ok=True);path.write_text(value)
        return runtime,formal,sources
    def test_fresh_packet_preserves_inputs_and_existing_four_spool_path(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);runtime,formal,sources=self.source_roots(root)
            before={str(p):p.read_bytes() for p in sources};destination=root/'packet'
            manifest=staging.prepare(destination,runtime,formal)
            self.assertEqual({str(p):p.read_bytes() for p in sources},before)
            self.assertFalse(manifest['qualification']);self.assertFalse(manifest['certification'])
            self.assertEqual(len(manifest['sources']),8)
            note=(destination/'runtime/crates/crypto/circuits/src/note.rs').read_text()
            self.assertEqual(note.count('group::witness_subgroup('),1)
            self.assertEqual(note.count('rk.assert_non_identity();'),1)
            exporter=(destination/'formal/integration/src/bin/transfer-ownership-inspection.rs').read_text()
            self.assertIn('rk-subgroup-spool',exporter);self.assertIn('shieldd-transfer-rk-subgroup-v1',exporter)
            for path,digest in manifest['sources'].items():self.assertEqual(hashlib.sha256((destination/path).read_bytes()).hexdigest(),digest)
            with self.assertRaisesRegex(RelationError,'fresh'):staging.prepare(destination,runtime,formal)
    def test_changed_or_duplicate_hook_refuses_before_packet_creation(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);runtime,formal,_=self.source_roots(root)
            note=runtime/'crates/crypto/circuits/src/note.rs';note.write_text(note.read_text()*2)
            with self.assertRaisesRegex(RelationError,'hook source shape'):staging.prepare(root/'packet',runtime,formal)
            self.assertFalse((root/'packet').exists())

    def test_future_note_output_map_resources_and_exporter_modes_survive(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);runtime,formal,sources=self.source_roots(root)
            note=runtime/'crates/crypto/circuits/src/note.rs'
            note.write_text('pub mod output_inspection;\npub mod output_hash_inspection;\n'+note.read_text()+
                            'fn constrain_output() { let _scope = output_inspection::scope(); }\n')
            catalogue=runtime/'crates/crypto/circuits/src/catalogue.rs'
            catalogue.write_text(catalogue.read_text()+'include!("catalogue/note_output_catalogue.rs");\n'
                                 'include!("catalogue/note_output_hash_catalogue.rs");\n'
                                 'include!("catalogue/balance_map_catalogue.rs");\n')
            exporter=formal/'integration/src/bin/transfer-ownership-inspection.rs'
            exporter.write_text(exporter.read_text()+'include!("../observers/note_output_export.rs");\n'
                                'fn compare_all_original_spools() {}\nfn repeated_observations_equal() {}\n'
                                'fn capture_note_pages() {}\nfn capture_map() {}\n')
            map_source=runtime/'crates/crypto/circuits/src/map.rs';map_source.write_text('// distinct future map lane\n')
            before={p:p.read_bytes() for p in [note,catalogue,exporter,map_source]}
            packet=root/'packet';staging.prepare(packet,runtime,formal)
            for p,value in before.items():self.assertEqual(p.read_bytes(),value)
            staged_note=(packet/'runtime/crates/crypto/circuits/src/note.rs').read_text()
            self.assertIn('pub mod output_hash_inspection;',staged_note)
            self.assertIn('let _scope = output_inspection::scope();',staged_note)
            staged_catalogue=(packet/'runtime/crates/crypto/circuits/src/catalogue.rs').read_text()
            for included in ('note_output_catalogue','note_output_hash_catalogue','balance_map_catalogue','rk_inspection'):
                self.assertEqual(staged_catalogue.count(included+'.rs'),1)
            staged_exporter=(packet/'formal/integration/src/bin/transfer-ownership-inspection.rs').read_text()
            for function in ('compare_all_original_spools','repeated_observations_equal','capture_note_pages','capture_map'):
                self.assertEqual(staged_exporter.count(function+'()'),1)
            self.assertFalse((packet/'runtime/crates/crypto/circuits/src/map.rs').exists())

    def merged_roots(self,root):
        runtime,formal,_=self.source_roots(root);parent=root/'source65';controls=root/'source06';clean=root/'clean'
        parent.mkdir();controls.mkdir();pin='844389ee069e1fb2e576708842d0b389b4d9a44a'
        group='crates/crypto/circuits/src/group.rs';recorder='crates/crypto/circuits/src/group/inspection.rs'
        digest=lambda data:hashlib.sha256(data).hexdigest()
        group_before=(runtime/group).read_bytes()
        group_after=group_before+b'\n#[cfg(test)]\n#[path = "group/formal_scalar_codec_tests.rs"]\nmod formal_scalar_codec_tests;\n'
        sdk={group:digest(group_after),recorder:digest((runtime/recorder).read_bytes())}
        sdk.update({f'crates/crypto/circuits/src/base{i}.rs':'0'*64 for i in range(49)})
        inventories={'sdk-source.txt':sdk,'compiler-source.txt':{f'third_party/commonware/cryptography/src/zk/file{i}.rs':'0'*64 for i in range(20)},
            'app-source.txt':{'crates/core/app/src/lib.rs':'0'*64},'runtime-inputs.txt':{'Cargo.lock':'0'*64},
            'formal-exporters.txt':{f'crates/crypto/circuits/examples/transfer{i}.rs':'0'*64 for i in range(8)}}
        for name,records in inventories.items():
            (controls/name).write_text(''.join(d+'  '+p+'\n' for p,d in sorted(records.items())))
        for suffix in ('before','after'):
            (controls/('clean-head-'+suffix+'.txt')).write_text(pin+'\n');(controls/('clean-status-'+suffix+'.txt')).write_text('')
        (controls/'overlay.json').write_text(json.dumps(dict(group_base_sha256=digest(group_before),group_after_sha256=digest(group_after))))
        for name in ('catalogue_shapes.rs','export_poseidon.rs'):
            target=clean/'crates/crypto/circuits/examples'/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_text('fn main() {}\n')
        payloads={
            'crates/crypto/circuits/src/note.rs':(runtime/'crates/crypto/circuits/src/note.rs').read_bytes(),
            'crates/crypto/circuits/src/catalogue.rs':b'include!("catalogue/transfer_t4_pages_catalogue.rs");\n',
            'crates/crypto/circuits/examples/transfer-ownership-inspection.rs':
                (formal/'integration/src/bin/transfer-ownership-inspection.rs').read_bytes()+b'fn ordinary() {}\nfn pages() {}\n"ordinary-spool" "fixed-spend-spool" "roles-spool" "qualify-spools" "transfer-t4-pages-spool"\n'}
        payloads.update({f'crates/crypto/circuits/src/future{i}.rs':b'// future module\n' for i in range(27)})
        mapping={};files={}
        for i,(relative,data) in enumerate(payloads.items()):
            path=f'payload{i}.rs';mapping[relative]=path;files[path]=digest(data);(parent/path).write_bytes(data)
        (parent/'manifest.json').write_text(json.dumps(dict(pin=pin,qualification=False,certification=False,files=files,overlay=mapping,inputs={},activation_base_files={})))
        return runtime,formal,parent,controls,clean

    def test_merged_complete_exporter_inventory_and_fresh_recipe(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);runtime,formal,parent,controls,clean=self.merged_roots(root)
            dest=root/'merged';m=staging.prepare_merged(dest,parent,controls,runtime,formal,clean_runtime_root=clean)
            self.assertEqual(len(m['overlay']),35);self.assertEqual(len(m['source06_inventory']['exporters']),10)
            self.assertEqual(len(m['clean_pin_examples']),2)
            self.assertIn('crates/crypto/circuits/src/transfer_rk_subgroup_export.rs',m['overlay'])
            self.assertNotIn('crates/crypto/circuits/examples/transfer_rk_subgroup.rs',m['overlay'])
            script=(dest/'stage.sh').read_text();self.assertIn("find crates/crypto/circuits/examples -type f -name '*.rs'",script)
            self.assertNotIn('cargo ',script);self.assertNotIn('lake ',script)
            self.assertFalse(m['qualification']);self.assertFalse(m['certification'])
            for path,d in m['recipe_files'].items():self.assertEqual(hashlib.sha256((dest/path).read_bytes()).hexdigest(),d)

    def test_merged_changed_parent_payload_refuses_before_destination(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);runtime,formal,parent,controls,clean=self.merged_roots(root)
            (parent/'payload0.rs').write_bytes(b'changed')
            with self.assertRaisesRegex(RelationError,'payload identity'):
                staging.prepare_merged(root/'merged',parent,controls,runtime,formal,clean_runtime_root=clean)
            self.assertFalse((root/'merged').exists())


if __name__=='__main__':unittest.main()
