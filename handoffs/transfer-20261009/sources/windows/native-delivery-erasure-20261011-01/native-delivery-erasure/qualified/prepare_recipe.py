"""Prepare exact Item/body/index equality from bounded primitive/raw erasure."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-native-ghost-erasure-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-native-raw-pending-20261011-03'", "UPSTREAM = DIAG / 'transfer-native-ghost-erasure-20261011-02'")
replace("POOL = DIAG / 'transfer-native-ghost-erasure-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-native-delivery-erasure-owned-floor-20261011-01'")
replace("MODULE = 'TransferNativeGhostErasure01'", "MODULE = 'TransferNativeDeliveryErasure01'")
s=s.replace("'runs/01-TransferNativeRawPending01/stdout.txt'", "'runs/01-TransferNativeGhostErasure01/stdout.txt'",1)
replace('assert len(current) == 3','assert len(current) == 5')
replace("records.append(('TransferNativeRawPending01'", "records.append(('TransferNativeGhostErasure01'")
replace("    'handwritten/TransferNativeRawPending01.lean', 'project/ShielddSecurity/TransferNativeRawPending01.lean']]", "    'handwritten/TransferNativeGhostErasure01.lean', 'project/ShielddSecurity/TransferNativeGhostErasure01.lean']]")
replace('assert len(records) == 74 and len(audits) == 724', 'assert len(records) == 75 and len(audits) == 729')
replace("'objects': 74", "'objects': 75")
s=s.replace('seventy-four-module','seventy-five-module').replace('724 inherited','729 inherited')
replace("'imports': ['ShielddSecurity.TransferNativeRawPending01']", "'imports': ['ShielddSecurity.TransferNativeGhostErasure01']")
replace('assert len(names) == 5','assert len(names) == 4')
replace("'fresh_audits': 5", "'fresh_audits': 4")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Accepted bounded canonical primitive/raw source-model ghost erasure lifted through exact complete-Item capability re-extraction and both proof contexts. Actual note/SCT/ordinary volume callback installation commutes with ghost/native-only source encoders. Exact bound body equality on every returned outcome, including errors, under actual initial pending invariant/canonical values and action input canonical domain. Generic exact enclosing delivery equality in every index mode follows only equality of actual initial-child body result; same index/height callbacks reused, no desired success/poststate/queue supplied. Four complete proofs, no definitions. This is symbolic source-model extension equality, not actual Rust trace or native codec/getter/input/library/callback/ownership/OS refinement. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh capability/installed complete-Item body and generic exact delivery equality, continuing accepted bounded raw ghost erasure. Qualified ghost02 five full reports reused with entire 729-report/75-module closure without replay. Historical failed originals retained and physical/per-run guards unchanged.'"+s[end:]
s=s.replace('SOURCE_BOUNDED_NATIVE_PENDING_GHOST_ERASURE_ALL_RETURN_PRIMITIVE_AND_RAW','SOURCE_BOUNDED_NATIVE_PENDING_GHOST_ERASURE_CAPABILITY_BODY_AND_DELIVERY')
s=s.replace('NATIVE_GHOST_ERASURE_COMPLETE_SEVENTY_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','NATIVE_DELIVERY_ERASURE_COMPLETE_SEVENTY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 724", "'inherited_audits': 729")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':4,'inherited_reports':729,'owned_modules':75})
