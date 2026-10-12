from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-canonical-source-publication-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-canonical-source-publication-20261011-01'","CURRENT = DIAG / 'transfer-canonical-source-membership-20261011-02'"),
 ("MODULE = 'TransferCanonicalSourcePublication01'","MODULE = 'TransferCanonicalSourceMembership01'"),
 ("CHECKPOINT = DIAG / 'transfer-canonical-source-publication-checkpoint-20261011-01'","CHECKPOINT = DIAG / 'transfer-canonical-source-membership-checkpoint-20261011-02'"),
 ("manager_endpoint = DIAG / 'transfer-canonical-source-word-retention-endpoint-20261011-02'","manager_endpoint = DIAG / 'transfer-canonical-source-publication-endpoint-20261011-02'"),
 ("manager_archive = manager_endpoint / 'portable-windows-canonical-source-word-retention-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-canonical-source-publication-endpoint01.tar.xz'"),
 ('5820d77836a349d7fd1735513c8c986900b46822de80c7327447a6deb16b33f5','02d0e580fc0168ac1540073a08a2765746ffa758d2aeae940d3e8f8bec562165'),
 ("tar.extractfile('reports/fresh-3-complete-declarations.txt')","tar.extractfile('reports/fresh-5-complete-declarations.txt')"),
 ('assert len(manager_reports) == 3','assert len(manager_reports) == 5'),
 ("'module': 'TransferCanonicalSourceWordRetention01'","'module': 'TransferCanonicalSourcePublication01'"),
 ("reference = {'canonical_source_word_retention':","reference = {'canonical_source_publication':"),
 ("'imported_complete_reports': 3","'imported_complete_reports': 5")]:replace(a,b)
s=s.replace('128','129').replace('1082','1087')
replace('assert len(fresh) == 5','assert len(fresh) == 6')
replace("assert declaration_kinds.count('def') == 2 and declaration_kinds.count('theorem') == 3","assert declaration_kinds.count('def') == 1 and declaration_kinds.count('theorem') == 5")
replace("add(stdout, 'reports/fresh-5-complete-declarations.txt'","add(stdout, 'reports/fresh-6-complete-declarations.txt'")
replace("'fresh_complete_public_audits': 5","'fresh_complete_public_audits': 6")
replace("'fresh_audits': 5, 'inherited_audits': 1087","'fresh_audits': 6, 'inherited_audits': 1087",2)
s=s.replace('transfer-canonical-source-publication-endpoint-v1','transfer-canonical-source-membership-endpoint-v1').replace('one-hundred-twenty-eight-module','one-hundred-twenty-nine-module').replace('CANONICAL_SOURCE_WHOLE_BLOCK_ORIGINAL_FIELDS_AND_CHECKED_SCT_PUBLICATION_QUALIFIED','CANONICAL_SOURCE_ORD_MEMBERSHIP_AND_ORIGINAL_FIELD_UNIQUENESS_QUALIFIED')
replace("archive = ROOT / 'portable-windows-canonical-source-publication-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-canonical-source-membership-endpoint01.tar.xz'")
start=s.index("superseded = DIAG / ");end=s.index("review = {'status':",start)
s=s[:start]+s[end:]
replace("'metadata_correction': metadata_history, ","")
replace("'rejected_attempts': 0","'rejected_attempts': 1")
at=s.index("row=mapping['sct_pending_read_source_shape']")
s=s[:at]+"pressure=DIAG/'transfer-canonical-source-membership-20261011-01'\nfor name in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCanonicalSourceMembership01.lean','project/ShielddSecurity/TransferCanonicalSourceMembership01.lean','runs/01-TransferCanonicalSourceMembership01/stdout.txt']:\n    row=pin(pressure/name)\n    assert row in plan['pins']\n    add(pressure/name,'rejected-membership-attempt01/'+name,'original physical pressure stopped attempt, zero stdout/audits/objects, zero credit')\n"+s[at:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Six complete full type/axiom reports retained, one definition/five theorems. Original canonical-field key injectivity, source Ord equality/membership and mapped-key uniqueness correspondence derive original source-field uniqueness/capacity from successful constructed whole execution. Exact failed pressure attempt01 retained, all attempts of that failure zero credit. Corrected source-kind counters automatically derived; corrected parent metadata histories preserved in ancestry. Native binding OPEN; no native/control/certification or accepted ancestor replay credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-canonical-source-membership-checkpoint-20261011-02';checkpoint.mkdir(exist_ok=False)
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-canonical-source-publication-checkpoint-20261011-01/preservation_check.py').read_bytes())
print({'fresh_reports':6,'inherited_reports':1087,'owned_modules':129,'pressure_history':True})
