from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-invert-field-endpoint-20261012-03/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-invert-field-20261012-03'","CURRENT = DIAG / 'transfer-scalar-inverse-correctness-20261012-04'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-invert-field-checkpoint-20261012-03'","CHECKPOINT = DIAG / 'transfer-scalar-inverse-correctness-checkpoint-20261012-04'"),
 ("MODULE = 'TransferScalarInvertField01'","MODULE = 'TransferScalarInverseCorrectness01'"),
 ("manager_endpoint = DIAG / 'transfer-scalar-field-values-endpoint-20261012-01'","manager_endpoint = DIAG / 'transfer-scalar-invert-field-endpoint-20261012-03'"),
 ("manager_archive = manager_endpoint / 'portable-windows-scalar-field-values-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-invert-field-endpoint01.tar.xz'"),
 ('154f551c0d7c0a32e08f126acaf931b05ed097af7287e9205da07f6ffe3f1a38','f2b15f75a23678c33590aad11df4c302a79575628dcc34ccc05adbcd5843db1e'),
 ("'module': 'TransferScalarFieldValues01'","'module': 'TransferScalarInvertField01'"),
 ("reference = {'scalar_field_values':","reference = {'scalar_invert_field':"),
 ('assert len(fresh) == 7','assert len(fresh) == 6'),
 ('assert len(manager_reports) == 4','assert len(manager_reports) == 7'),
 ("manager_stdout = tar.extractfile('reports/fresh-4-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-7-complete-declarations.txt')"),
 ("assert declaration_kinds.count('inductive') == 0 and declaration_kinds.count('def') == 1 and declaration_kinds.count('theorem') == 6","assert declaration_kinds.count('inductive') == 0 and declaration_kinds.count('def') == 0 and declaration_kinds.count('theorem') == 6"),
 ("archive = ROOT / 'portable-windows-scalar-invert-field-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-inverse-correctness-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-7-complete-declarations.txt'","add(stdout, 'reports/fresh-6-complete-declarations.txt'"),
 ("assert pool['objects'] == 161 and len(pool['inherited_public_reports']) == 1283","assert pool['objects'] == 202 and len(pool['inherited_public_reports']) == 1416")]:replace(a,b)
foundation="""assert len(combined_reports)==1290 and len(manager_selected)==162
inverseContext=json.loads((CURRENT/'context/scalar-inverse-correctness-shape.json').read_text())
fieldArchive=inverseContext['field_original_archive']
assert pin(fieldArchive['path'])==fieldArchive and fieldArchive in plan['pins']
assert fieldArchive['sha256']=='95306c503a4c36027919716ff75fd4766301772c85d193d3a9678730c7f8f3cc'
fieldReceipts=inverseContext['field_original_qualified_receipts']
assert pin(fieldReceipts['path'])==fieldReceipts and fieldReceipts in plan['pins']
fieldReports={}
with tarfile.open(fieldArchive['path'],'r:xz') as fieldTar:
    rows=json.loads(fieldTar.extractfile('receipts/qualified-modules.json').read())
    assert len(rows)==48 and sum(row['audit_pairs'] for row in rows)==167
    selectedField=[row for row in rows if row['module'] in {'ModularPower','LucasCertificate'}|{'FieldPrimeNode%02d'%n for n in range(1,39)}]
    assert len(selectedField)==40
    for row in selectedField:
        receipt=row['receipt'];assert receipt['status']=='passed'
        task=DIAG/row['task'];originalPlan=json.loads((task/'plan.json').read_text())
        originalTarget=next(target for target in originalPlan['targets'] if target['module']==row['module'])
        raw=fieldTar.extractfile('audit-output/'+row['module']+'.txt').read()
        assert len(raw)==receipt['stdout']['bytes'] and hashlib.sha256(raw).hexdigest()==receipt['stdout']['sha256']
        complete=m.audit(raw.decode(),originalTarget['audit_names'])
        assert len(complete)==row['audit_pairs'] and complete==receipt['audits']
        assert set(fieldReports).isdisjoint(complete) and set(combined_reports).isdisjoint(complete)
        fieldReports.update(complete)
        prefix='generated-source' if row['module'].startswith('FieldPrimeNode') else 'handwritten-source'
        sourceRaw=fieldTar.extractfile(prefix+'/ShielddSecurity/'+row['module']+'.lean').read()
        assert sourceRaw==Path(row['source']['path']).read_bytes()
        assert pin(row['source']['path'])==row['source']==originalTarget['source']
        assert len(receipt['objects'])==1 and pin(receipt['objects'][0]['path'])==receipt['objects'][0]
        manager_selected.append({'module':row['module'],'source':row['source'],'object':receipt['objects'][0]})
assert len(fieldReports)==126 and fieldReports==pool['field_foundation']['reports']
combined_reports.update(fieldReports)
assert len(combined_reports)==1416 and combined_reports==pool['inherited_public_reports']
assert len(manager_selected)==202
"""
replace("assert len(combined_reports) == 1283 and combined_reports == pool['inherited_public_reports']\nassert len(manager_selected) == 161",foundation)
replace("if name.startswith('source/ShielddSecurity/') and name.endswith('.lean')","if name.endswith('.lean') and name.startswith(('source/ShielddSecurity/','generated-source/ShielddSecurity/','handwritten-source/ShielddSecurity/'))")
replace('carriers = [pin(manager_archive)]','carriers = [pin(manager_archive),fieldArchive]')
old="""        if member in originals:
            assert originals[member] == Path(selected['source']['path']).read_bytes()
            found = True
            break"""
new="""        candidates=[name for name in originals if name.endswith('/ShielddSecurity/'+selected['module']+'.lean')]
        for name in candidates:
            if originals[name]==Path(selected['source']['path']).read_bytes():
                found=True;break
        if found:break"""
replace(old,new)
replace("assert plan['external_floor'] in list(core_floor_refs(manager_reference))","fieldOriginalPlan=DIAG/'transfer-prime-tree-closed-20261010-05/plan.json'\nassert json.loads(fieldOriginalPlan.read_text())['external_floor']==plan['external_floor']\nassert pin(fieldOriginalPlan) in plan['pins']")
replace("dump(ROOT / 'inherited-reference.json', reference)","reference['field_foundation']={'archive':fieldArchive,'manifest':inverseContext['field_original_manifest'],'original_qualified_receipts':fieldReceipts,'original_packet_modules':48,'original_packet_reports':167,'selected_whole_prime_branch_modules':40,'selected_complete_reports':126,'all_selected_source_object_and_complete_reports_verified':True,'external_floor':{'original':plan['external_floor'],'original_qualified_plan':pin(fieldOriginalPlan)},'scope':'Exact original whole40-module Lucas/ModularPower/38-node prime branch reused without replay; original full48-module167-report packet unchanged. Report sets disjoint from whole162-module1290-report word closure.'}\nreference['scope']='Complete202-module first owned root and1416 original complete reports: whole162-module word closure and exact original40-module prime branch. Full source/object/report identities verified; original field48-module packet retained unchanged; no ancestors replayed.'\ndump(ROOT / 'inherited-reference.json', reference)")
replace("for name in ['prepare.py', 'prepare_recipe.py', 'execute_bounded.py',","for name in ['prepare.py', 'prepare_recipe.py', 'prepare_recipe_from01.py', 'execute_bounded.py',")
s=s.replace('one-hundred-sixty-one-module','two-hundred-two-module').replace('1283 original inherited complete reports','1416 original inherited complete reports').replace('verified 1283 inherited reports','verified 1416 inherited reports')
start=s.index('for attempt in [1,2]:');end=s.index("row=mapping['scalar_invert_field_source_shape']",start)
history="""for attempt in [1,2,3]:
    prior=DIAG/('transfer-scalar-inverse-correctness-20261012-%02d'%attempt)
    if attempt==1:
        names=['prepare_recipe.py','handwritten/TransferScalarInverseCorrectness01.lean']
        assert not (prior/'prepare.py').exists()
    else:
        names=['prepare_recipe.py','prepare_recipe_from01.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/scalar-inverse-correctness-shape.json','handwritten/TransferScalarInverseCorrectness01.lean','project/ShielddSecurity/TransferScalarInverseCorrectness01.lean']
        if attempt==2:assert not (prior/'events.jsonl').exists()
        else:names+=['events.jsonl','runs/01-TransferScalarInverseCorrectness01/stdout.txt']
    for name in names:
        row=pin(prior/name);assert row in plan['pins']
        add(prior/name,'prior-inverse-attempt%02d/'%attempt+name,'original setup gap/unrun metadata predecessor/failed Lean attempt retained with complete written stdout; no qualified result')
row=mapping['scalar_inverse_correctness_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-inverse-correctness-shape.json','exact previously qualified prime branch and field exponent source association; modeled inverse correctness, native binding separate')
add(fieldReceipts['path'],'context/field-foundation-original-full48-qualified.json','unchanged original full48-module167-report qualified source/object/complete-report receipts; selected whole40-module126-report prime branch verified')
"""
s=s[:start]+history+s[end:]
old=' Seven complete declarations:one definition/six theorems. Symbolic operand/register/step/walk correspondence derives exact source85-statement inversion payload field value input^(p-2) modulo p. Original21 raw failed-attempt artifacts retained, including full failed Lean output. Only two proof-script lines repaired; source algorithm/conclusions/contracts/guards unchanged. Fermat/field inversion and native compiler/caller/full Transfer remain open. No ancestors replayed.'
new=' Six complete theorem declarations. Exact previously qualified modulus primality, derived source-chain field exponent, locally proved finite-unit-cardinality Fermat consequence and canonical-value injectivity derive modeled inversion product1, exact raw ONE after modeled multiplication and refusal iff mathematical zero. Original24 prior raw artifacts retained, including complete failed Lean output. Two congrArg beta simplifications repaired; source algorithm/conclusions/contracts/guards unchanged. Original40-module126-report prime branch reused without replay; original field48-module167-report packet unchanged. Native compiler/Choice/library/caller/full Transfer remain open.'
replace(old,new)
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-inverse-correctness-checkpoint-20261012-04';checkpoint.mkdir()
shutil.copyfile(DIAG/'transfer-scalar-invert-field-checkpoint-20261012-03/preservation_check.py',checkpoint/'preservation_check.py')
print({'fresh_reports':6,'inherited_reports':1416,'whole_owned_modules':202,'original_field_branch_modules':40,'original_field_reports':126,'prior_raw_artifacts':24,'assembly_not_run':True})
