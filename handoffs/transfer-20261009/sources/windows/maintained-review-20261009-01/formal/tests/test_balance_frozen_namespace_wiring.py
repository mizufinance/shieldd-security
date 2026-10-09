"""Execute only the frozen builder wrapper with the semantic build mocked.

No captured metadata, ordinary rows or generated proofs are constructed here.
"""
import ast,runpy,sys,unittest
from pathlib import Path
from unittest.mock import patch

P=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')

class FrozenNamespaceWiringTests(unittest.TestCase):
    def test_builder_entry_and_consumer_share_one_exact_namespace_definition(self):
        packet=P/'balance-joint-consumer-source-09'
        sys.path.insert(0,str(packet));sys.path.insert(0,str(packet/'source'))
        try:
            import driver
            from integration import transfer_balance_actual_spec as actual
            driver.source_check()
            with patch.object(actual,'build',return_value=Path('wrapper-only-test')) as build:
                runpy.run_path(str(packet/'build-spec.py'),run_name='wrapper_import_fixture')
                build.assert_called_once_with(packet.parent,packet.parent/actual.INPUT_PACKET)
            tree=ast.parse((packet/'driver.py').read_bytes())
            owned=[node for node in ast.walk(tree) if isinstance(node,ast.Assign)
                and any(isinstance(target,ast.Name) and target.id=='owned' for target in node.targets)]
            self.assertEqual(len(owned),1)
            self.assertIn('actual_spec.JOINT_PACKET',ast.unparse(owned[0].value))
            builder=ast.parse((packet/'source/integration/transfer_balance_actual_spec.py').read_bytes())
            destination=[node.value for node in ast.walk(builder) if isinstance(node,ast.keyword) and node.arg=='destination']
            self.assertEqual(len(destination),1)
            self.assertIn('root / JOINT_PACKET',ast.unparse(destination[0]))
            self.assertIn('/'+actual.JOINT_PACKET,(P/'balance-joint-actual-17.ps1').read_text())
            endpoint=(P/'balance-native-endpoint-post-joint-source-07/driver.py').read_text()
            self.assertIn('prior=P/actual_spec.JOINT_PACKET',endpoint)
            self.assertIn('out=P/actual_spec.ENDPOINT_PACKET',endpoint)
            self.assertIn('/'+actual.ENDPOINT_PACKET,(P/'balance-native-endpoint-post-joint-07.ps1').read_text())
        finally:
            sys.path.pop(0);sys.path.pop(0)
