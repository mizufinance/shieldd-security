import copy,json,unittest
from pathlib import Path
from validate_records import validate_node
ROOT=Path(__file__).resolve().parents[2]
DATA=json.loads((ROOT/'outputs/mac-poseidon-round01/rounds03.json').read_text())
NODES=[n for scope in DATA['selected_rounds'] for n in scope['nodes']]
class SourceCertificateGuards(unittest.TestCase):
 def test_actual_nodes(self):
  self.assertEqual(len(NODES),251)
  for node in NODES:validate_node(node)
 def test_add_mul_mismatch(self):
  node=copy.deepcopy(next(n for n in NODES if n['operation']=='add'))
  node['operation']='mul'
  with self.assertRaisesRegex(ValueError,'raw mul'):validate_node(node)
 def test_mul_add_mismatch(self):
  node=copy.deepcopy(next(n for n in NODES if n['certificate']['constructor']=='product'))
  node['operation']='add'
  with self.assertRaisesRegex(ValueError,'raw add'):validate_node(node)
 def test_rewired_existing_source_port(self):
  node=copy.deepcopy(next(n for n in NODES if n['certificate']['constructor']=='product'))
  node['left']=copy.deepcopy(node['right'])
  self.assertNotEqual(node['left'],node['certificate']['left'])
  with self.assertRaisesRegex(ValueError,'operand mismatch'):validate_node(node)
 def test_duplicate_product_row(self):
  node=copy.deepcopy(next(n for n in NODES if n['certificate']['constructor']=='product'))
  node['certificate']['rows'][1]=node['certificate']['rows'][0]
  with self.assertRaisesRegex(ValueError,'row shape'):validate_node(node)
if __name__=='__main__':unittest.main()
