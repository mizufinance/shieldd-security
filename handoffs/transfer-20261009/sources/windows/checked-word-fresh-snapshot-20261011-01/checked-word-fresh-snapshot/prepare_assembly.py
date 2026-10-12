from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-checked-word-known-finalization-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-checked-word-known-finalization-20261011-01'","CURRENT = DIAG / 'transfer-checked-word-fresh-snapshot-20261011-01'"),
 ("CHECKPOINT = DIAG / 'transfer-checked-word-known-finalization-checkpoint-20261011-01'","CHECKPOINT = DIAG / 'transfer-checked-word-fresh-snapshot-checkpoint-20261011-01'"),
 ("MODULE = 'TransferCheckedWordKnownFinalization01'","MODULE = 'TransferCheckedWordFreshSnapshot01'"),
 ("manager_endpoint = DIAG / 'transfer-checked-word-block-driver-endpoint-20261011-03'","manager_endpoint = DIAG / 'transfer-checked-word-known-finalization-endpoint-20261011-01'"),
 ("manager_archive = manager_endpoint / 'portable-windows-checked-word-block-driver-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-checked-word-known-finalization-endpoint01.tar.xz'"),
 ('83725803ba90213196712e308234ff1de4e633900db5daec884c83befeecc4f8','7a25106d853f69da0c578107cf8cf2a8c513cb1b86311af4bbd247ba3e045545'),
 ("'module': 'TransferCheckedWordBlockDriver01'","'module': 'TransferCheckedWordKnownFinalization01'"),
 ("reference = {'checked_word_block_driver':","reference = {'checked_word_known_finalization':"),
 ("assert declaration_kinds.count('def') == 2 and declaration_kinds.count('theorem') == 3","assert declaration_kinds.count('def') == 3 and declaration_kinds.count('theorem') == 2")]:replace(a,b)
s=s.replace('== 141','== 142').replace('== 1153','== 1158').replace("'inherited_complete_public_audits': 1153","'inherited_complete_public_audits': 1158")
replace("'fresh_audits': 5, 'inherited_audits': 1153","'fresh_audits': 5, 'inherited_audits': 1158",2)
s=s.replace('transfer-checked-word-known-finalization-endpoint-v1','transfer-checked-word-fresh-snapshot-endpoint-v1').replace('one-hundred-forty-one-module','one-hundred-forty-two-module').replace('1153 original inherited complete reports','1158 original inherited complete reports').replace('verified 1153 inherited reports','verified 1158 inherited reports').replace('CHECKED_WORD_BLOCK_ORIGINAL_FIELD_GETTER_SURVIVES_KNOWN_SIX_SOURCE_MUTATIONS_QUALIFIED','SOURCE_SHAPED_FRESH_SNAPSHOT_DISCHARGES_CHECKED_WORD_DRIVER_INITIAL_ABSENCE_QUALIFIED')
replace("archive = ROOT / 'portable-windows-checked-word-known-finalization-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-checked-word-fresh-snapshot-endpoint01.tar.xz'")
at=s.index("row=mapping['checked_word_seal_source_shape']")
s=s[:at]+"row=mapping['fresh_snapshot_source_shape']\nassert pin(row['path'])==row and row in plan['pins']\nadd(row['path'],'context/source-fresh-snapshot-shape.json','exact Snapshot object None/StateDelta new live default leaf/no layers/cache default declarations; static association, no durable/ICS23/native semantic credit')\n"+s[at:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Five complete audits, three definitions/two theorems. Source-shaped fresh snapshot object reads None and empty live leaf/no-layer constructor discharge absence and checked default/unsealed getters. Constructed whole checked-word public walk/seal derives actual original global field getter, uniqueness/capacity/canonical durable false observations and frames from whole-run success only. No caller initial absence/invariant/codec/getter/domain premise. Persistent data/reader semantics independent, native constructor/locks/default-map/caller/compiler/ICS23 bindings OPEN. First attempt passes; no ancestors replayed.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-checked-word-fresh-snapshot-checkpoint-20261011-01';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-checked-word-known-finalization-checkpoint-20261011-01/preservation_check.py').read_bytes())
print({'fresh_reports':5,'inherited_reports':1158,'owned_modules':142,'counts_derived_from_originals':True})
