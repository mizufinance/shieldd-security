"""Bounded source/retained-row fixtures; no replay, proof generation or adoption."""
import ast,copy,hashlib,json,unittest
from pathlib import Path
from unittest.mock import patch
from circuits import transfer_balance_input_layout as layout,transfer_balance_joint_rows as joint
from circuits import transfer_relation as relation

P=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')

class BalanceRetainedConsumerTests(unittest.TestCase):
    def test_frozen_successor_has_no_ordinary_open_and_coherent_namespaces(self):
        packet=P/'balance-joint-consumer-source-15'
        manifest=json.loads((packet/'manifest.json').read_bytes())
        for relative,digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((packet/relative).read_bytes()).hexdigest(),digest)
        for raw,digest in manifest['inputs'].items():
            self.assertEqual(hashlib.sha256(Path(raw).read_bytes()).hexdigest(),digest)
        driver=(packet/'driver.py').read_text();compile(driver,str(packet/'driver.py'),'exec')
        compile((packet/'build-spec.py').read_bytes(),str(packet/'build-spec.py'),'exec')
        self.assertNotIn("Path(spec['ordinary']).open",driver)
        self.assertIn('joint.reaccept_retained',driver)
        self.assertIn('ordinary_replays=0,parent_ordinary_replays=1',driver)
        self.assertIn('actual_spec.JOINT_PACKET',driver)
        self.assertEqual(manifest['namespaces']['joint'],'balance-joint-actual-13')
        self.assertIn('/balance-joint-actual-13', (P/'balance-joint-actual-23.ps1').read_text())
        endpoint_packet=P/'balance-native-endpoint-post-joint-source-16'
        endpoint=(endpoint_packet/'driver.py').read_text()
        compile(endpoint,str(endpoint_packet/'driver.py'),'exec')
        self.assertIn('ordinary_replays=0,parent_ordinary_replays=1',endpoint)
        self.assertIn('balance-joint-actual-23-guard',endpoint)
        self.assertNotIn('parent_ordinary_replays=0,parent_ordinary_replays=1',endpoint)
        self.assertIn('/balance-native-endpoint-post-joint-actual-10',
                      (P/'balance-native-endpoint-post-joint-16.ps1').read_text())
        self.assertLess(endpoint.index('extraction=joint.reaccept_retained'),endpoint.index('name,body=group.generate'))
        self.assertEqual((endpoint_packet/'source/circuits/generate_transfer_balance_native_endpoint.py').read_bytes(),
                         (P/'balance-native-endpoint-post-joint-source-13/source/circuits/generate_transfer_balance_native_endpoint.py').read_bytes())

    def test_compile_rejects_duplicate_keywords_that_ast_accepts(self):
        bad='dict(ordinary_replays=0,parent_ordinary_replays=0,parent_ordinary_replays=1)'
        ast.parse(bad)
        with self.assertRaises(SyntaxError):compile(bad,'duplicate-keyword-control','exec')
        compile('dict(ordinary_replays=0,parent_ordinary_replays=1)','valid-replay-marker','exec')

    def test_group_inventory_is_derived_from_exact_reproduced_body(self):
        import re
        packet=P/'balance-joint-actual-13'
        name='RuntimeBalanceGroupComposition'
        source=(packet/'modules'/(name+'.lean')).read_text()
        checks=re.findall(r'^#check @([\w.]+)',source,re.M)
        audits=re.findall(r'^#print axioms ([\w.]+)',source,re.M)
        expected=['h_writes_checked','h_rows_checked','final_writes_checked','final_rows_checked',
                  'outside_column','outside_eval','constructs']
        self.assertEqual(checks,audits)
        self.assertEqual(checks,expected)
        inventory=json.loads((packet/'module-inventory.json').read_bytes())[name]
        self.assertEqual(inventory['full_signatures'],checks)
        self.assertEqual(inventory['axiom_commands'],audits)
        endpoint=(P/'balance-native-endpoint-post-joint-source-16/driver.py').read_text()
        self.assertIn("inventory[name]['full_signatures']!=group_checks",endpoint)
        self.assertNotIn("len(inventory[name]['full_signatures'])!=5",endpoint)

    def test_retained_final_arithmetic_unchanged_when_frame_is_corrected(self):
        raw=(P/'balance-joint-actual-09/extraction.json').read_bytes()
        self.assertEqual(hashlib.sha256(raw).hexdigest(),
                         '096094c19d5266ffb60f69d7fb6ef4359df6d5023a1c9f3eb69dc0852353fef1')
        extraction=json.loads(raw)
        spec=json.loads((P/'balance-joint-actual-inputs-05/activation-spec.json').read_bytes())
        readonly=[tuple(tuple(term) for term in lc) for lc in spec['readonly_lcs']
                  if lc!=[[22734,1]]]
        readonly.extend(((column,1),) for column in layout.public_witness_shadows(extraction['identity']))
        # Isolate the frame/row rechecker. Actual semantic ingress is exercised
        # only by the root driver; this mock does not construct accepted roles.
        def typed(value):
            if isinstance(value,list):return tuple(typed(item) for item in value)
            if isinstance(value,dict):return {key:typed(item) for key,item in value.items()}
            return value
        typed_source=typed(extraction['parents'])
        with patch.object(joint.addition,'from_ingress',return_value=typed_source):
            accepted=joint.reaccept_retained(extraction,*([None]*10),readonly)
            self.assertIs(accepted['parents'],typed_source)
            self.assertEqual(accepted['final_add']['selected_rows'],extraction['final_add']['selected_rows'])
            self.assertEqual(json.loads(json.dumps(accepted['final_add']['stages'])),extraction['final_add']['stages'])
            self.assertIn(22737,accepted['final_add']['protected'])
            self.assertEqual(accepted['ordinary_replays'],1)
            changed=copy.deepcopy(extraction)
            changed['final_add']['selected_rows'][0]['a'][0][1]='2'
            with self.assertRaises(relation.RelationError):
                joint.reaccept_retained(changed,*([None]*10),readonly)
            changed=copy.deepcopy(extraction);changed['ordinary_replays']=0
            with self.assertRaises(relation.RelationError):
                joint.reaccept_retained(changed,*([None]*10),readonly)
