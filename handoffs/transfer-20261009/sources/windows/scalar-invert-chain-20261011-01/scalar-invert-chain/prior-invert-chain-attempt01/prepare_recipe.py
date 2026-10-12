from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-scalar-invert-machine-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-scalar-pow-invariant-20261011-01'","UPSTREAM = DIAG / 'transfer-scalar-invert-machine-20261011-01'"),
 ("POOL = DIAG / 'transfer-scalar-invert-machine-owned-floor-20261011-01'","POOL = DIAG / 'transfer-scalar-invert-chain-owned-floor-20261011-01'"),
 ("MODULE = 'TransferScalarInvertMachine01'","MODULE = 'TransferScalarInvertChain01'"),
 ("stdout = UPSTREAM / 'runs/01-TransferScalarPowInvariant01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferScalarInvertMachine01/stdout.txt'"),
 ('assert len(current) == 15','assert len(current) == 20'),
 ("records.append(('TransferScalarPowInvariant01'","records.append(('TransferScalarInvertMachine01'"),
 ("'handwritten/TransferScalarPowInvariant01.lean', 'project/ShielddSecurity/TransferScalarPowInvariant01.lean'","'handwritten/TransferScalarInvertMachine01.lean', 'project/ShielddSecurity/TransferScalarInvertMachine01.lean'"),
 ('assert len(names) == 20','assert len(names) == 9'),
 ("'imports': ['ShielddSecurity.TransferScalarPowInvariant01']","'imports': ['ShielddSecurity.TransferScalarInvertMachine01']"),
 ("handwritten = ROOT / 'handwritten' / (MODULE + '.lean')","handwritten = ROOT / 'generated' / (MODULE + '.lean')")]:replace(a,b)
s=s.replace('== 156','== 157').replace('== 1237','== 1257').replace("'objects': 156","'objects': 157").replace('one-hundred-fifty-six-module','one-hundred-fifty-seven-module').replace('1237 inherited','1257 inherited').replace("'inherited_audits': 1237","'inherited_audits': 1257")
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
scope='Exact authenticated cached source inversion addition chain generated from85 original ordered statements. Small generic register machine derives all reads initialized, successful canonical payload, and zero refusal projection. Separate finite natural-exponent machine certificate reaches actual modulus minus2. Three definitions/six theorems. Field exponent/inverse semantics, native Choice/ct_eq/library/compiler/ABI/caller/full Transfer OPEN; no native/runtime/control/replay/certification credit. Generated source repaired only through generator and fresh plan.'
s=s[:start]+"\nmapping = dict(prior_mapping)\nmapping['interfaces'] = prior_mapping['interfaces'] + ["+repr(scope)+"]\nmapping['scope'] = "+repr(scope)+s[end:]
replace("mapping['scalar_invert_machine_source_shape']=pin(ROOT/'context/scalar-invert-machine-shape.json')","mapping['scalar_invert_machine_source_shape']=pin(DIAG/'transfer-scalar-invert-machine-20261011-01/context/scalar-invert-machine-shape.json')\nmapping['scalar_invert_chain_source_shape']=pin(ROOT/'context/scalar-invert-chain-shape.json')")
replace("plan['pins'].append(mapping['scalar_invert_machine_source_shape'])","plan['pins'].append(mapping['scalar_invert_machine_source_shape'])\nplan['pins'].append(mapping['scalar_invert_chain_source_shape'])\nplan['pins'].append(pin(ROOT/'generate_source.py'))")
s=s.replace("'fresh_audits': 20","'fresh_audits': 9").replace('SCALAR_INVERT_MACHINE_COMPLETE_ONE_HUNDRED_FIFTY_SIX_MODULE','SCALAR_INVERT_CHAIN_COMPLETE_ONE_HUNDRED_FIFTY_SEVEN_MODULE')
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':9,'inherited_reports':1257,'owned_modules':157,'generated_source':True})
