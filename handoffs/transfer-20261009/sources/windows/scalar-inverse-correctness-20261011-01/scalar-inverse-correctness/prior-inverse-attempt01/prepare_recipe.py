from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
def pin(p):
    data=p.read_bytes();return {'path':str(p),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
upstream=DIAG/'transfer-scalar-invert-field-20261012-03'
events=[json.loads(line) for line in (upstream/'events.jsonl').read_text().splitlines()]
assert len(events)==2 and events[-1]['result']['status']=='passed'
fieldEndpoint=DIAG/'transfer-field-cardinality-endpoint-20261010-02'
qualified=fieldEndpoint/'packet/receipts/qualified-modules.json'
foundation=[r for r in json.loads(qualified.read_text()) if r['module'] in
    {'ModularPower','LucasCertificate'}|{'FieldPrimeNode%02d'%n for n in range(1,39)}]
assert len(foundation)==40
foundationReports=sum(r['audit_pairs'] for r in foundation)
floor=DIAG/'transfer-external-floor-complete-20261010-08/external-floor.json'
assert pin(floor)['sha256']=='82ef07658ca7d127e3e58c293946c87dfdb66dba4a94ad2683c9c7158e92ba72'
assert 'Mathlib.FieldTheory.Finite.Basic' in json.loads(floor.read_text())['modules']
(ROOT/'context').mkdir()
(ROOT/'context/scalar-inverse-correctness-shape.json').write_text(json.dumps({
 'scope':'Reuse exact previously qualified complete40-module Lucas prime-tree branch (ModularPower, LucasCertificate, all38 generated prime nodes); original full48-module field packet remains unchanged. Exact modulus proof has no caller primality premise. Fermat and canonical-value injectivity derive the source inversion multiplicative inverse/raw ONE/refusal semantics. Native Choice/compiler/caller remains separate.',
 'field_original_qualified_receipts':pin(qualified),'field_original_manifest':pin(fieldEndpoint/'packet/manifest.json'),
 'field_original_archive':pin(fieldEndpoint/'portable-windows-field-cardinality-endpoint01.tar.xz'),
 'reused_field_modules':40,'reused_field_reports':foundationReports,'external_floor':pin(floor),
 'word_source_instance':pin(upstream/'handwritten/TransferScalarInvertField01.lean')
},indent=2,sort_keys=True)+'\n')
s=(upstream/'prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-scalar-field-values-20261012-01'","UPSTREAM = DIAG / 'transfer-scalar-invert-field-20261012-03'"),
 ("POOL = DIAG / 'transfer-scalar-invert-field-owned-floor-20261012-03'","POOL = DIAG / 'transfer-scalar-inverse-correctness-owned-floor-20261012-01'"),
 ("MODULE = 'TransferScalarInvertField01'","MODULE = 'TransferScalarInverseCorrectness01'"),
 ("stdout = UPSTREAM / 'runs/01-TransferScalarFieldValues01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferScalarInvertField01/stdout.txt'"),
 ('assert len(current) == 4','assert len(current) == 7'),
 ("records.append(('TransferScalarFieldValues01'","records.append(('TransferScalarInvertField01'"),
 ("'handwritten/TransferScalarFieldValues01.lean', 'project/ShielddSecurity/TransferScalarFieldValues01.lean'","'handwritten/TransferScalarInvertField01.lean', 'project/ShielddSecurity/TransferScalarInvertField01.lean'"),
 ('assert len(names) == 7','assert len(names) == 6'),
 ("'imports': ['ShielddSecurity.TransferScalarFieldValues01']","'imports': ['ShielddSecurity.TransferScalarInvertField01', 'ShielddSecurity.FieldPrimeNode38', 'Mathlib.FieldTheory.Finite.Basic']")]:replace(a,b)
replace('assert len(records) == 161 and len(audits) == 1283','assert len(records) == 162 and len(audits) == 1290')
extra="""
fieldEndpoint=DIAG/'transfer-field-cardinality-endpoint-20261010-02'
fieldReceipts=fieldEndpoint/'packet/receipts/qualified-modules.json'
fieldRows=[r for r in json.loads(fieldReceipts.read_text()) if r['module'] in
    {'ModularPower','LucasCertificate'}|{'FieldPrimeNode%02d'%n for n in range(1,39)}]
assert len(fieldRows)==40
fieldReports={}
for row in fieldRows:
    receipt=row['receipt'];assert receipt['status']=='passed'
    task=DIAG/row['task']; originalPlan=json.loads((task/'plan.json').read_text())
    originalTarget=next(t for t in originalPlan['targets'] if t['module']==row['module'])
    assert pin(row['source']['path'])==row['source']==originalTarget['source']
    assert len(receipt['objects'])==1 and pin(receipt['objects'][0]['path'])==receipt['objects'][0]
    assert pin(receipt['stdout']['path'])==receipt['stdout']
    complete=m.audit(Path(receipt['stdout']['path']).read_text(),originalTarget['audit_names'])
    assert len(complete)==row['audit_pairs'] and complete==receipt['audits']
    assert set(fieldReports).isdisjoint(complete) and set(audits).isdisjoint(complete)
    fieldReports.update(complete)
    assert row['module'] not in {r[0] for r in records}
    records.append((row['module'],row['source'],receipt['objects'][0]))
    inputs += [pin(task/'plan.json'),pin(task/'events.jsonl'),pin(task/'execute_bounded.py'),row['source'],receipt['objects'][0],receipt['stdout']]
inputs += [pin(fieldReceipts),pin(fieldEndpoint/'packet/manifest.json'),pin(fieldEndpoint/'portable-windows-field-cardinality-endpoint01.tar.xz')]
audits.update(fieldReports)
assert len(records)==202 and len(audits)==1290+len(fieldReports)
"""
replace('POOL.mkdir()',extra+'\nPOOL.mkdir()')
replace("'objects': 161","'objects': 202")
replace("composition_file = POOL / 'composition-review.json'","composition['field_foundation']={'selected_modules':40,'selected_complete_reports':len(fieldReports),'reports':fieldReports,'original_qualified_receipts':pin(fieldReceipts),'original_full_field_archive':pin(fieldEndpoint/'portable-windows-field-cardinality-endpoint01.tar.xz'),'original_full48_packet_unchanged':True,'scope':'Exact whole40-module qualified prime-tree branch reused; no proof replay. Complete current162-module word closure retained; report sets disjoint and counted exactly.'}\ncomposition['objects']=len(selected)\ncomposition['scope']='Complete202-module first owned root: original162-module word closure plus complete40-module previously qualified Lucas prime-tree branch. All original complete reports and exact source/object identities retained without replay; original full48-module field packet unchanged. No native semantic assertion.'\ncomposition_file = POOL / 'composition-review.json'")
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
scope='Exact previously qualified modulus primality plus derived actual source85-statement inversion field exponent proves every returned modeled inverse has product1, exact raw ONE after modeled multiplication, and refusal iff mathematical zero. Six theorem audits. Complete40-module prime-tree branch reused without replay; original48-module field packet unchanged. Native Choice/library/compiler/ABI/caller/full Transfer remain open.'
s=s[:start]+"\nmapping = dict(prior_mapping)\nmapping['interfaces'] = prior_mapping['interfaces'] + ["+repr(scope)+"]\nmapping['scope'] = "+repr(scope)+s[end:]
replace("mapping['scalar_invert_field_source_shape']=pin(ROOT/'context/scalar-invert-field-shape.json')","mapping['scalar_invert_field_source_shape']=pin(DIAG/'transfer-scalar-invert-field-20261012-03/context/scalar-invert-field-shape.json')\nmapping['scalar_inverse_correctness_source_shape']=pin(ROOT/'context/scalar-inverse-correctness-shape.json')")
replace("plan['pins'].append(mapping['scalar_invert_field_source_shape'])","plan['pins'].append(mapping['scalar_invert_field_source_shape'])\nplan['pins'].append(mapping['scalar_inverse_correctness_source_shape'])")
replace("plan['owned_import_pool'] = pin(composition_file)","plan['external_floor']=pin(DIAG/'transfer-external-floor-complete-20261010-08/external-floor.json');plan['external_floor']['admission_ready']=True\nplan['lean_path']=[str(POOL/'modules'),str(ROOT/'project'),str(DIAG/'transfer-external-package-overlay-20261010-03/modules'),str(DIAG/'transfer-implementation-20261002/windows-jubjub-isolated-05/modules')]\nplan['owned_import_pool'] = pin(composition_file)")
s=s.replace("'fresh_audits': 7","'fresh_audits': 6").replace("'inherited_audits': 1283","'inherited_audits': len(audits)").replace('SCALAR_INVERT_FIELD_COMPLETE_ONE_HUNDRED_SIXTY_ONE_MODULE','SCALAR_INVERSE_CORRECTNESS_COMPLETE_TWO_HUNDRED_TWO_MODULE')
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':6,'inherited_word_reports':1290,'reused_field_reports':foundationReports,'whole_owned_modules':202,'prime_replay':False})
