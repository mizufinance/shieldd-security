from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-word-source-driver-endpoint-20261011-03/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-word-source-driver-20261011-03'","CURRENT = DIAG / 'transfer-word-object-read-20261011-03'"),
 ("MODULE = 'TransferWordSourceDriver01'","MODULE = 'TransferWordObjectRead01'"),
 ("CHECKPOINT = DIAG / 'transfer-word-source-driver-checkpoint-20261011-03'","CHECKPOINT = DIAG / 'transfer-word-object-read-checkpoint-20261011-03'"),
 ('assert len(fresh) == 5','assert len(fresh) == 8'),
 ("assert pool['objects'] == 119 and len(pool['inherited_public_reports']) == 1031","assert pool['objects'] == 120 and len(pool['inherited_public_reports']) == 1036"),
 ("manager_endpoint = DIAG / 'transfer-word-object-codec-endpoint-20261011-01'","manager_endpoint = DIAG / 'transfer-word-source-driver-endpoint-20261011-03'"),
 ("manager_archive = manager_endpoint / 'portable-windows-word-object-codec-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-word-source-driver-endpoint01.tar.xz'"),
 ('e40ca16debbd4c003ddd9fcaf955e0b300f319f166a3fcbb2ec907e57629922f','edb48a6ad5d6f6588575f18ff90f7940242d2971173f0224ea5fb11495dbed87'),
 ("tar.extractfile('reports/fresh-8-complete-declarations.txt')","tar.extractfile('reports/fresh-5-complete-declarations.txt')"),
 ('assert len(manager_reports) == 8','assert len(manager_reports) == 5'),
 ("'module': 'TransferWordObjectCodec01'","'module': 'TransferWordSourceDriver01'"),
 ('assert len(combined_reports) == 1031','assert len(combined_reports) == 1036'),
 ('assert len(manager_selected) == 119','assert len(manager_selected) == 120'),
 ("reference = {'word_object_codec':","reference = {'word_source_driver':"),
 ("'imported_complete_reports': 8","'imported_complete_reports': 5"),
 ("'complete_owned_modules': 119, 'inherited_complete_reports': 1031","'complete_owned_modules': 120, 'inherited_complete_reports': 1036"),
 ("'fresh_definition_audits': 2","'fresh_definition_audits': 3"),
 ("'fresh_theorem_audits': 3","'fresh_theorem_audits': 5"),
 ("'fresh_complete_public_audits': 5","'fresh_complete_public_audits': 8"),
 ("'inherited_complete_public_audits': 1031","'inherited_complete_public_audits': 1036"),
 ("archive = ROOT / 'portable-windows-word-source-driver-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-word-object-read-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-5-complete-declarations.txt'","add(stdout, 'reports/fresh-8-complete-declarations.txt'")]:replace(a,b)
replace("'fresh_audits': 5, 'inherited_audits': 1031","'fresh_audits': 8, 'inherited_audits': 1036",2)
s=s.replace('transfer-word-source-driver-endpoint-v1','transfer-word-object-read-endpoint-v1').replace('one-hundred-nineteen-module','one-hundred-twenty-module').replace('1031 original inherited','1036 original inherited').replace('verified 1031 inherited','verified 1036 inherited')
s=s.replace('WHOLE_RETURNED_WORD_FIELD_SOURCE_DRIVER_AND_PUBLICATION_QUALIFIED','CHECKED_TYPED_WORD_OBJECT_GETTER_PANIC_AND_TOMBSTONE_BRANCHES_QUALIFIED')
start=s.index('for attempt,names in [(1,');end=s.index("row = mapping['r2_decoder_payload_source_shape']",start)
history="""for attempt,names in [(1,['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','handwritten/TransferWordObjectRead01.lean','project/ShielddSecurity/TransferWordObjectRead01.lean','context/checked-pending-read-shape.json']),
    (2,['repair_recipe.py','prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordObjectRead01.lean','project/ShielddSecurity/TransferWordObjectRead01.lean','context/checked-pending-read-shape.json'])]:
    failed=DIAG/('transfer-word-object-read-20261011-'+str(attempt).zfill(2))
    for name in names:
        assert pin(failed/name) in plan['pins']
        add(failed/name,'unselected/'+str(attempt).zfill(2)+'/'+name,'original setup01 trailing mkdir error or pre-Lean pressure02 retained; zero proof/native/control credit')
row=mapping['checked_pending_read_source_shape']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'],'context/checked-pending-read-shape.json','exact source getter downcast-before-Clone leaf/layer/parent branches and pending absence default; static association only')
"""
s=s[:start]+history+s[end:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Eight complete full type/axiom reports retained, three definitions/five theorems. Actual modeled successful checked read recovers canonical bounded sealed finite enum and agrees with previous projection only on success. Present wrong-type panic sentinel never defaults; latest tombstone masks underlying object and returns absence. Setup01 trailing mkdir exception after files were prepared retained UNRUN; pressure02 before Lean retained; twenty original raw files with zero credit. Fresh03 same source as02 and unchanged guards. Panic sentinel is outside native Rust Result, not a recoverable refusal or executed negative control. No native/compiler/Any/Clone/layer/imbl semantic credit. Full Transfer OPEN.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':8,'inherited_reports':1036,'owned_modules':120,'history_files':20})
