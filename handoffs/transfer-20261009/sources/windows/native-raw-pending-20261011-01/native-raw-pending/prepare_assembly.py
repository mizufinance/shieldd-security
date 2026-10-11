"""Seal fixed-codec any-return raw pending retention and failed originals."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-native-pending-write-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-native-pending-write-20261011-01'", "CURRENT = DIAG / 'transfer-native-raw-pending-20261011-03'")
s=s.replace('transfer-native-pending-write-checkpoint-20261011-01','transfer-native-raw-pending-checkpoint-20261011-03').replace('native-pending-write-endpoint','native-raw-pending-endpoint')
replace("MODULE = 'TransferNativePendingWrite01'", "MODULE = 'TransferNativeRawPending01'")
replace("assert pool['objects'] == 72 and len(pool['inherited_public_reports']) == 718", "assert pool['objects'] == 73 and len(pool['inherited_public_reports']) == 721")
replace("manager_endpoint = DIAG / 'transfer-native-seal-transfer-endpoint-20261011-03'", "manager_endpoint = DIAG / 'transfer-native-pending-write-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-native-seal-transfer-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-native-pending-write-endpoint01.tar.xz'")
replace('7257f945b81834122a4250780738409aa50c60c34623218e789780be6e715451','368417e6166149697c80e4301d20ef679f78b23be08d9b5a6021b2e1c800c82d')
replace("'module': 'TransferNativeSealTransfer01'", "'module': 'TransferNativePendingWrite01'")
replace('assert len(combined_reports) == 718','assert len(combined_reports) == 721')
replace('assert len(manager_selected) == 72','assert len(manager_selected) == 73')
replace("reference = {'native_seal_transfer':", "reference = {'native_primitive_write':")
replace("'complete_owned_modules': 72, 'inherited_complete_reports': 718", "'complete_owned_modules': 73, 'inherited_complete_reports': 721")
s=s.replace('seventy-two-module','seventy-three-module').replace('718 original inherited','721 original inherited').replace('verified 718 inherited','verified 721 inherited')
replace("'fresh_definition_audits': 0", "'fresh_definition_audits': 1")
replace("'fresh_theorem_audits': 3", "'fresh_theorem_audits': 2")
replace("'inherited_complete_public_audits': 718", "'inherited_complete_public_audits': 721")
replace("'fresh_audits': 3, 'inherited_audits': 718", "'fresh_audits': 3, 'inherited_audits': 721",2)
replace('SOURCE_SUPPORTED_CANONICAL_NATIVE_PENDING_PRIMITIVE_WRITES_QUALIFIED','SOURCE_FIXED_CODEC_NATIVE_PENDING_RETAINED_IN_ANY_RETURNED_RAW_RESHAPE_QUALIFIED')
replace("'rejected_attempts': 0", "'rejected_attempts': 2")
anchor="add(stdout, 'reports/fresh-3-complete-declarations.txt'";i=s.index(anchor)
extra="""for suffix in ['01','02']:
    failed=DIAG/('transfer-native-raw-pending-20261011-'+suffix)
    failed_events=[json.loads(line) for line in (failed/'events.jsonl').read_text().splitlines()]
    assert len(failed_events)==2 and failed_events[-1]['result']['status']=='failed'
    for name in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferNativeRawPending01.lean','project/ShielddSecurity/TransferNativeRawPending01.lean','runs/01-TransferNativeRawPending01/stdout.txt']:
        assert pin(failed/name) in plan['pins']
        add(failed/name,'rejected/source'+suffix+'/'+name,'strict failed proof elaboration; original retained with zero whole-proof or semantic control credit')
"""
s=s[:i]+extra+s[i:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' One definition and two original complete full types/axioms retained. Fixed finite source encoder removes the extra primitive encoder premise; original all-return notes/SCT frames retain the actual native pending object even when later reshape errors. Failed01/02 preserved whole0, source03 proof-only normalization. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':3,'inherited_reports':721,'owned_modules':73,'rejected_attempts':2})
