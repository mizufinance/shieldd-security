from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-word-object-put-endpoint-20261011-03/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-word-object-put-20261011-03'","CURRENT = DIAG / 'transfer-word-sct-pending-read-20261011-01'"),
 ("MODULE = 'TransferWordObjectPut01'","MODULE = 'TransferWordSctPendingRead01'"),
 ("CHECKPOINT = DIAG / 'transfer-word-object-put-checkpoint-20261011-03'","CHECKPOINT = DIAG / 'transfer-word-sct-pending-read-checkpoint-20261011-01'"),
 ("assert pool['objects'] == 125 and len(pool['inherited_public_reports']) == 1063","assert pool['objects'] == 126 and len(pool['inherited_public_reports']) == 1071"),
 ("manager_endpoint = DIAG / 'transfer-word-layer-flatten-endpoint-20261011-03'","manager_endpoint = DIAG / 'transfer-word-object-put-endpoint-20261011-03'"),
 ("manager_archive = manager_endpoint / 'portable-windows-word-layer-flatten-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-word-object-put-endpoint01.tar.xz'"),
 ('bce2913d5b200269c695776982274d49974db229d719ea6a410c35124a2215f6','7259fe8a640eb7ead7a68a71553a3ac354db9e5e143fca377a477b39036842f1'),
 ("tar.extractfile('reports/fresh-4-complete-declarations.txt')","tar.extractfile('reports/fresh-8-complete-declarations.txt')"),
 ('assert len(manager_reports) == 4','assert len(manager_reports) == 8'),
 ("'module': 'TransferWordLayerFlatten01'","'module': 'TransferWordObjectPut01'"),
 ('assert len(combined_reports) == 1063','assert len(combined_reports) == 1071'),
 ('assert len(manager_selected) == 125','assert len(manager_selected) == 126'),
 ("reference = {'word_layer_flatten':","reference = {'word_object_put':"),
 ("'imported_complete_reports': 4","'imported_complete_reports': 8"),
 ("'complete_owned_modules': 125, 'inherited_complete_reports': 1063","'complete_owned_modules': 126, 'inherited_complete_reports': 1071"),
 ("'inherited_complete_public_audits': 1063","'inherited_complete_public_audits': 1071"),
 ("'rejected_attempts': 2","'rejected_attempts': 0"),
 ("archive = ROOT / 'portable-windows-word-object-put-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-word-sct-pending-read-endpoint01.tar.xz'")]:replace(a,b)
replace("'fresh_audits': 8, 'inherited_audits': 1063","'fresh_audits': 8, 'inherited_audits': 1071",2)
s=s.replace('transfer-word-object-put-endpoint-v1','transfer-word-sct-pending-read-endpoint-v1').replace('one-hundred-twenty-five-module','one-hundred-twenty-six-module').replace('1063 original inherited','1071 original inherited').replace('verified 1063 inherited','verified 1071 inherited')
s=s.replace('FIXED_PENDING_TYPE_GUARDED_OBJECT_PUT_AND_CHECKED_READ_QUALIFIED','SOURCE_SCT_PENDING_GETTER_ABSENCE_OPEN_SEALED_AND_PANIC_BRANCHES_QUALIFIED')
start=s.index('for attempt in [1,2]:');end=s.index("row=mapping['checked_pending_put_source_shape']",start)
s=s[:start]+s[end:]
at=s.index("row=mapping['checked_pending_put_source_shape']")
s=s[:at]+"row=mapping['sct_pending_read_source_shape']\nassert pin(row['path']) == row and row in plan['pins']\nadd(row['path'],'context/sct-pending-read-shape.json','exact source typed enum/default/ordered clone/isSealed/ensureSealed cases; absence passes ensure while isSealed false; static association only')\n"+s[at:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Eight first-pass complete full type/axiom reports retained, three definitions/five theorems. Typed absence yields empty ordered vector, false sealed status and successful ensure; Open returns ordered vector plus returned open refusal; Sealed returns vector/true/success. Wrong type outer panic sentinel occurs before default or inner returned refusal. Explicit absent witness proves ensure success does not imply present sealed enum. Native downcast/Clone/imbl/Scalar/compiler/owner/liveness semantics remain separate; prior histories preserved in original ancestor archives/pins. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':8,'inherited_reports':1071,'owned_modules':126,'first_pass':True})
