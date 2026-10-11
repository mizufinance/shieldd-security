"""Seal exact bounded model erasure with full audits and failed original."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-native-raw-pending-endpoint-20261011-03/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-native-raw-pending-20261011-03'", "CURRENT = DIAG / 'transfer-native-ghost-erasure-20261011-02'")
s=s.replace('transfer-native-raw-pending-checkpoint-20261011-03','transfer-native-ghost-erasure-checkpoint-20261011-02').replace('native-raw-pending-endpoint','native-ghost-erasure-endpoint')
replace("MODULE = 'TransferNativeRawPending01'", "MODULE = 'TransferNativeGhostErasure01'")
replace('assert len(fresh) == 3','assert len(fresh) == 5')
replace("assert pool['objects'] == 73 and len(pool['inherited_public_reports']) == 721", "assert pool['objects'] == 74 and len(pool['inherited_public_reports']) == 724")
replace("manager_endpoint = DIAG / 'transfer-native-pending-write-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-native-raw-pending-endpoint-20261011-03'")
replace("manager_archive = manager_endpoint / 'portable-windows-native-pending-write-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-native-raw-pending-endpoint01.tar.xz'")
replace('368417e6166149697c80e4301d20ef679f78b23be08d9b5a6021b2e1c800c82d','fc91e3068055cfbf8e10b857ecc00048c9ad0e617a59e627aa354c88856a8dbb')
replace("'module': 'TransferNativePendingWrite01'", "'module': 'TransferNativeRawPending01'")
replace('assert len(combined_reports) == 721','assert len(combined_reports) == 724')
replace('assert len(manager_selected) == 73','assert len(manager_selected) == 74')
replace("reference = {'native_primitive_write':", "reference = {'native_raw_pending':")
replace("'complete_owned_modules': 73, 'inherited_complete_reports': 721", "'complete_owned_modules': 74, 'inherited_complete_reports': 724")
s=s.replace('seventy-three-module','seventy-four-module').replace('721 original inherited','724 original inherited').replace('verified 721 inherited','verified 724 inherited')
replace("'fresh_theorem_audits': 2", "'fresh_theorem_audits': 4")
replace("'fresh_complete_public_audits': 3", "'fresh_complete_public_audits': 5")
replace("'inherited_complete_public_audits': 721", "'inherited_complete_public_audits': 724")
replace("'fresh_audits': 3, 'inherited_audits': 721", "'fresh_audits': 5, 'inherited_audits': 724",2)
replace('SOURCE_FIXED_CODEC_NATIVE_PENDING_RETAINED_IN_ANY_RETURNED_RAW_RESHAPE_QUALIFIED','SOURCE_BOUNDED_CANONICAL_PENDING_GHOST_ERASURE_ALL_RETURN_PRIMITIVE_RAW_QUALIFIED')
replace("'rejected_attempts': 2", "'rejected_attempts': 1")
start=s.index("for suffix in ['01','02']:");end=s.index("add(stdout, 'reports/fresh-3-complete-declarations.txt'",start)
extra="""failed=DIAG/'transfer-native-ghost-erasure-20261011-01'
failed_events=[json.loads(line) for line in (failed/'events.jsonl').read_text().splitlines()]
assert len(failed_events)==2 and failed_events[-1]['result']['status']=='failed'
for name in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferNativeGhostErasure01.lean','project/ShielddSecurity/TransferNativeGhostErasure01.lean','runs/01-TransferNativeGhostErasure01/stdout.txt']:
    assert pin(failed/name) in plan['pins']
    add(failed/name,'rejected/source01/'+name,'strict failed parser/elaboration original, zero whole-proof/control credit')
"""
s=s[:start]+extra+s[end:]
replace("add(stdout, 'reports/fresh-3-complete-declarations.txt'", "add(stdout, 'reports/fresh-5-complete-declarations.txt'")
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' One definition and four original complete full types/axioms retained. Exact symbolic equality erases unsupported encoder ghosts for all returned primitive and raw outcomes under bounded canonical actual arguments and identical callbacks. This is not native Rust trace refinement or native codec/getter closure. Failed01 retained whole0; source02 proof-only case normalization. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':5,'inherited_reports':724,'owned_modules':74,'rejected_attempts':1})
