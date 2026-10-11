from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-word-object-codec-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-word-object-codec-20261011-01'","CURRENT = DIAG / 'transfer-word-source-driver-20261011-03'"),
 ("MODULE = 'TransferWordObjectCodec01'","MODULE = 'TransferWordSourceDriver01'"),
 ("CHECKPOINT = DIAG / 'transfer-word-object-codec-checkpoint-20261011-01'","CHECKPOINT = DIAG / 'transfer-word-source-driver-checkpoint-20261011-03'"),
 ('assert len(fresh) == 8','assert len(fresh) == 5'),
 ("assert pool['objects'] == 118 and len(pool['inherited_public_reports']) == 1023","assert pool['objects'] == 119 and len(pool['inherited_public_reports']) == 1031"),
 ("manager_endpoint = DIAG / 'transfer-canonical-word-pending-endpoint-20261011-03'","manager_endpoint = DIAG / 'transfer-word-object-codec-endpoint-20261011-01'"),
 ("manager_archive = manager_endpoint / 'portable-windows-canonical-word-pending-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-word-object-codec-endpoint01.tar.xz'"),
 ('188197fc7ad7a27c9d2f9b5332f901f8845a2095910f1ce71f238af8312e97f5','e40ca16debbd4c003ddd9fcaf955e0b300f319f166a3fcbb2ec907e57629922f'),
 ("'module': 'TransferCanonicalWordPending01'","'module': 'TransferWordObjectCodec01'"),
 ('assert len(combined_reports) == 1023','assert len(combined_reports) == 1031'),
 ('assert len(manager_selected) == 118','assert len(manager_selected) == 119'),
 ("reference = {'canonical_word_pending':","reference = {'word_object_codec':"),
 ("'complete_owned_modules': 118, 'inherited_complete_reports': 1023","'complete_owned_modules': 119, 'inherited_complete_reports': 1031"),
 ("'fresh_definition_audits': 4","'fresh_definition_audits': 2"),
 ("'fresh_theorem_audits': 4","'fresh_theorem_audits': 3"),
 ("'fresh_complete_public_audits': 8","'fresh_complete_public_audits': 5"),
 ("'inherited_complete_public_audits': 1023","'inherited_complete_public_audits': 1031"),
 ("'rejected_attempts': 0","'rejected_attempts': 1, 'unrun_setup_attempts': 1"),
 ("archive = ROOT / 'portable-windows-word-object-codec-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-word-source-driver-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-8-complete-declarations.txt'","add(stdout, 'reports/fresh-5-complete-declarations.txt'")]:replace(a,b)
replace("'fresh_audits': 8, 'inherited_audits': 1023","'fresh_audits': 5, 'inherited_audits': 1031",2)
s=s.replace('transfer-word-object-codec-endpoint-v1','transfer-word-source-driver-endpoint-v1').replace('one-hundred-eighteen-module','one-hundred-nineteen-module').replace('1023 original inherited','1031 original inherited').replace('verified 1023 inherited','verified 1031 inherited')
s=s.replace('CONCRETE_TYPED_WORD_OBJECT_CODEC_AND_SEALED_GETTER_QUALIFIED','WHOLE_RETURNED_WORD_FIELD_SOURCE_DRIVER_AND_PUBLICATION_QUALIFIED')
at=s.index("row = mapping['r2_decoder_payload_source_shape']")
history="""for attempt,names in [(1,['prepare_recipe.py','prepare.py','handwritten/TransferWordSourceDriver01.lean']),
    (2,['repair_recipe.py','prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordSourceDriver01.lean','project/ShielddSecurity/TransferWordSourceDriver01.lean'])]:
    failed=DIAG/('transfer-word-source-driver-20261011-'+str(attempt).zfill(2))
    for name in names:
        assert pin(failed/name) in plan['pins']
        add(failed/name,'unselected/'+str(attempt).zfill(2)+'/'+name,'original setup01 or pre-Lean physical-pressure02 retained; zero proof/native/control credit')
"""
s=s[:at]+history+s[at:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Five complete full type/axiom reports retained: two definitions and three theorems. Successful actual modeled empty-start request walk derives canonical bounded supported sealed codec domain. Word-field scalar/list/object roundtrip instantiates known source-ordered finalization and whole returned execution, deriving exact global mathematical inputs and same frozen/application/physical commit boundary. No supplied desired final object, walk/current state, codec/getter/domain or key-injection premise in returned driver theorem. Setup01 report-order check and pressure02 pre-Lean stop retained as thirteen complete original raw files with zero proof/control credit. Fresh03 same source/guards. Native imbl/private Scalar/Any/downcast/Clone/compiler/primitive/Choice/CtOption/full callee/value/trace/ownership/OS bindings and older extended ghost carrier remain explicit. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':5,'inherited_reports':1031,'owned_modules':119,'history_files':13})
