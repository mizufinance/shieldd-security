from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-checked-word-fresh-snapshot-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-checked-word-fresh-snapshot-20261011-01'","CURRENT = DIAG / 'transfer-checked-word-accepted-input-20261011-02'"),
 ("CHECKPOINT = DIAG / 'transfer-checked-word-fresh-snapshot-checkpoint-20261011-01'","CHECKPOINT = DIAG / 'transfer-checked-word-accepted-input-checkpoint-20261011-02'"),
 ("MODULE = 'TransferCheckedWordFreshSnapshot01'","MODULE = 'TransferCheckedWordAcceptedInput01'"),
 ("manager_endpoint = DIAG / 'transfer-checked-word-known-finalization-endpoint-20261011-01'","manager_endpoint = DIAG / 'transfer-checked-word-fresh-snapshot-endpoint-20261011-01'"),
 ("manager_archive = manager_endpoint / 'portable-windows-checked-word-known-finalization-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-checked-word-fresh-snapshot-endpoint01.tar.xz'"),
 ('7a25106d853f69da0c578107cf8cf2a8c513cb1b86311af4bbd247ba3e045545','b2f49a56b38d065e140f368d388ce861bc363508bb9ff663e9b7e192b919228f'),
 ("'module': 'TransferCheckedWordKnownFinalization01'","'module': 'TransferCheckedWordFreshSnapshot01'"),
 ("reference = {'checked_word_known_finalization':","reference = {'checked_word_fresh_snapshot':"),
 ("assert len(fresh) == 5","assert len(fresh) == 4"),
 ("assert declaration_kinds.count('def') == 3 and declaration_kinds.count('theorem') == 2","assert declaration_kinds.count('def') == 1 and declaration_kinds.count('theorem') == 3"),
 ("archive = ROOT / 'portable-windows-checked-word-fresh-snapshot-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-checked-word-accepted-input-endpoint01.tar.xz'")]:replace(a,b)
s=s.replace('== 142','== 143').replace('== 1158','== 1163')
s=s.replace('one-hundred-forty-two-module','one-hundred-forty-three-module').replace('1158 original inherited complete reports','1163 original inherited complete reports').replace('verified 1158 inherited reports','verified 1163 inherited reports')
s=s.replace("add(stdout, 'reports/fresh-5-complete-declarations.txt'","add(stdout, 'reports/fresh-4-complete-declarations.txt'")
s=s.replace("'fresh_complete_public_audits': 5","'fresh_complete_public_audits': len(fresh)").replace("'inherited_complete_public_audits': 1158","'inherited_complete_public_audits': len(pool['inherited_public_reports'])")
s=s.replace("'fresh_audits': 5, 'inherited_audits': 1158","'fresh_audits': len(fresh), 'inherited_audits': len(pool['inherited_public_reports'])")
s=s.replace("'rejected_attempts': 0","'rejected_attempts': 1")
s=s.replace('transfer-checked-word-fresh-snapshot-endpoint-v1','transfer-checked-word-accepted-input-endpoint-v1').replace('SOURCE_SHAPED_FRESH_SNAPSHOT_DISCHARGES_CHECKED_WORD_DRIVER_INITIAL_ABSENCE_QUALIFIED','ACTUAL_FRESH_CHECKED_WORD_GETTER_DERIVES_EXACT_ACCEPTED_CANONICAL_KEY_VECTOR_QUALIFIED')
at=s.index("row=mapping['fresh_snapshot_source_shape']")
extra="""failed=DIAG/'transfer-checked-word-accepted-input-20261011-01'
for name in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCheckedWordAcceptedInput01.lean','project/ShielddSecurity/TransferCheckedWordAcceptedInput01.lean','runs/01-TransferCheckedWordAcceptedInput01/stdout.txt','context/checked-word-accepted-source-shape.json']:
    row=pin(failed/name)
    assert row in plan['pins']
    add(failed/name,'rejected-accepted-input-attempt01/'+name,'original finite heartbeat proof error and full placeholder reports; entire attempt zero credit, not a negative control')
row=mapping['checked_word_accepted_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/checked-word-accepted-source-shape.json','exact source ordered getter then iter/copied/collect and writer prepare call shapes; static association only, native vector/Copy/Scalar/compiler bindings separate')
"""
s=s[:at]+extra+s[at:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Four complete audits, one definition/three theorems. Actual fresh whole-block getter determines the accepted ordered key vector and exact Montgomery values, key uniqueness/capacity/canonical bounds and durable false observations; every original field serializes to32 bytes. No caller initial absence/invariant/getter/domain/codec/intermediate-walk premise. Original heartbeat failure retained11 raw artifacts zero credit; explicit alias unfolding repair only, definitions/contracts/guards unchanged. Native Vec/Copy/private Scalar/reader/ABI/compiler/Host/writer binding and full Transfer OPEN; no ancestors replayed.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-checked-word-accepted-input-checkpoint-20261011-02';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-checked-word-fresh-snapshot-checkpoint-20261011-01/preservation_check.py').read_bytes())
print({'fresh_reports':4,'inherited_reports':1163,'owned_modules':143})
