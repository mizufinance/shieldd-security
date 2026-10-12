from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
def pin(p):
    p=Path(p);b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
(ROOT/'context').mkdir()
pool=json.loads((DIAG/'transfer-scalar-inverse-correctness-20261012-04/plan.json').read_text())
owned=json.loads(Path(pool['owned_import_pool']['path']).read_text())
certificate=next(row['source'] for row in owned['selected'] if row['module']=='FieldPrimeNode38')
context={'public_constants':pin(DIAG/'transfer-scalar-public-constants-20261011-02/handwritten/TransferScalarPublicConstants01.lean'),'original_generator_prime_certificate':certificate,'modular_power':next(row['source'] for row in owned['selected'] if row['module']=='ModularPower'),'order_source':pin(DIAG.parent.parent/'circuits/.lake/packages/mathlib/Mathlib/GroupTheory/OrderOfElement.lean'),'scope':'Exact source public Montgomery generator/root/inverse/DELTA mathematical powers and multiplicative orders. Reuse original complete Lucas prime tree unchanged, bounded binary modular checks only. Native bindings/compiler/library/caller/full Transfer remain separate.'}
(ROOT/'context/scalar-public-orders-shape.json').write_text(json.dumps(context,indent=2,sort_keys=True)+'\n')
s=(DIAG/'transfer-scalar-pow-field-20261012-03/prepare.py').read_text()
start=s.index("bits=DIAG/");end=s.index('originalInputs=inputs[:]',start);s=s[:start]+s[end:]
start=s.index("composition['shared_word_branch']=");end=s.index('composition_file =',start)
s=s[:start]+"composition['scope']='Complete203-module first owned root and1422 complete original reports: whole qualified inverse/prime foundation reused without replay. Exact source/object/report identities preserved.'\n"+s[end:]
s=s.replace("POOL = DIAG / 'transfer-scalar-pow-field-owned-floor-20261012-03'","POOL = DIAG / 'transfer-scalar-public-orders-owned-floor-20261012-01'").replace("MODULE = 'TransferScalarPowField01'","MODULE = 'TransferScalarPublicOrders01'")
s=s.replace("'objects': 204","'objects': 203").replace('assert len(names) == 6','assert len(names) == 7').replace("'fresh_audits': 6","'fresh_audits': 7")
s=s.replace("mapping['scalar_pow_bit_integer_source_shape']=pin(bits/'context/scalar-pow-bit-integer-shape.json')\n",'')
s=s.replace('scalar_pow_field_source_shape','scalar_public_orders_source_shape').replace('scalar-pow-field-shape.json','scalar-public-orders-shape.json')
s=s.replace("'imports': ['ShielddSecurity.TransferScalarInverseCorrectness01', 'ShielddSecurity.TransferScalarPowBitInteger01']","'imports': ['ShielddSecurity.TransferScalarInverseCorrectness01', 'Mathlib.GroupTheory.OrderOfElement']")
start=s.index("unrunPower=DIAG/");end=s.index("plan['artifact_policy']",start);s=s[:start]+s[end:]
s=s.replace("'SCALAR_POW_FIELD_COMPLETE_TWO_HUNDRED_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN'","'SCALAR_PUBLIC_ORDERS_COMPLETE_TWO_HUNDRED_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN'")
s=s.replace("mapping['scope'] =", "mapping['scope'] =",1)
start=s.index("mapping['scope'] =");end=s.index('\n',start)
s=s[:start]+"mapping['scope'] = json.loads((ROOT/'context/scalar-public-orders-shape.json').read_text())['scope']"+s[end:]
s=s.replace('complete204-module owned root with exact shared word foundation and qualified prime/bit branches','complete203-module owned root with qualified word/prime/inverse foundation')
(ROOT/'prepare.py').write_text(s)
print({'fresh_theorems':7,'inherited_modules':203,'inherited_complete_reports':1422,'original_lucas_tree_reused_without_replay':True})
