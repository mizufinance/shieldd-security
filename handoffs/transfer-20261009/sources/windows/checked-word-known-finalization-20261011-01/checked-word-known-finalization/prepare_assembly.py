from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-checked-word-block-driver-endpoint-20261011-03/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-checked-word-block-driver-20261011-03'","CURRENT = DIAG / 'transfer-checked-word-known-finalization-20261011-01'"),
 ("CHECKPOINT = DIAG / 'transfer-checked-word-block-driver-checkpoint-20261011-03'","CHECKPOINT = DIAG / 'transfer-checked-word-known-finalization-checkpoint-20261011-01'"),
 ("MODULE = 'TransferCheckedWordBlockDriver01'","MODULE = 'TransferCheckedWordKnownFinalization01'"),
 ("manager_endpoint = DIAG / 'transfer-checked-word-walk-endpoint-20261011-01'","manager_endpoint = DIAG / 'transfer-checked-word-block-driver-endpoint-20261011-03'"),
 ("manager_archive = manager_endpoint / 'portable-windows-checked-word-walk-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-checked-word-block-driver-endpoint01.tar.xz'"),
 ('ad0af22d5d27bf6583dea92e4393c53c8f51fba27f8f7f511e0f2d6674da6669','83725803ba90213196712e308234ff1de4e633900db5daec884c83befeecc4f8'),
 ("'module': 'TransferCheckedWordWalk01'","'module': 'TransferCheckedWordBlockDriver01'"),
 ("reference = {'checked_word_walk':","reference = {'checked_word_block_driver':"),
 ('assert len(manager_reports) == 4','assert len(manager_reports) == 5'),
 ("manager_stdout = tar.extractfile('reports/fresh-4-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-5-complete-declarations.txt')"),
 ("'rejected_attempts': 2","'rejected_attempts': 0")]:replace(a,b)
s=s.replace('== 140','== 141').replace('== 1148','== 1153').replace("'inherited_complete_public_audits': 1148","'inherited_complete_public_audits': 1153")
replace("'fresh_audits': 5, 'inherited_audits': 1148","'fresh_audits': 5, 'inherited_audits': 1153",2)
s=s.replace('transfer-checked-word-block-driver-endpoint-v1','transfer-checked-word-known-finalization-endpoint-v1').replace('one-hundred-forty-module','one-hundred-forty-one-module').replace('1148 original inherited complete reports','1153 original inherited complete reports').replace('verified 1148 inherited reports','verified 1153 inherited reports').replace('CONSTRUCTED_WHOLE_CHECKED_WORD_BLOCK_DERIVES_ACTUAL_ORIGINAL_GLOBAL_FIELD_GETTER_QUALIFIED','CHECKED_WORD_BLOCK_ORIGINAL_FIELD_GETTER_SURVIVES_KNOWN_SIX_SOURCE_MUTATIONS_QUALIFIED')
replace("archive = ROOT / 'portable-windows-checked-word-block-driver-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-checked-word-known-finalization-endpoint01.tar.xz'")
start=s.index('for attempt in [1,2]:');end=s.index("row=mapping['checked_word_seal_source_shape']",start)
s=s[:start]+s[end:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Five complete audits, two definitions/three theorems. Actual original-field getter derived from complete checked public block/checked seal survives the corrected six known source object mutations by symbolic key-frame lemma. Exact source key order and value vector show one tree put/five tombstones and no unsupported ghost conversion in constructed recipe. Tree object remains supplied native parameter; hidden callees/full App trace/native binding OPEN. First attempt passes; no ancestors replayed.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-checked-word-known-finalization-checkpoint-20261011-01';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-checked-word-block-driver-checkpoint-20261011-03/preservation_check.py').read_bytes())
print({'fresh_reports':5,'inherited_reports':1153,'owned_modules':141,'counts_derived_from_originals':True})
