"""Prepare exact request step and symbolic bounded block-walk erasure."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-native-delivery-erasure-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-native-ghost-erasure-20261011-02'", "UPSTREAM = DIAG / 'transfer-native-delivery-erasure-20261011-01'")
replace("POOL = DIAG / 'transfer-native-delivery-erasure-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-native-reachable-erasure-owned-floor-20261011-01'")
replace("MODULE = 'TransferNativeDeliveryErasure01'", "MODULE = 'TransferNativeReachableErasure01'")
s=s.replace("'runs/01-TransferNativeGhostErasure01/stdout.txt'", "'runs/01-TransferNativeDeliveryErasure01/stdout.txt'",1)
replace('assert len(current) == 5','assert len(current) == 4')
replace("records.append(('TransferNativeGhostErasure01'", "records.append(('TransferNativeDeliveryErasure01'")
replace("    'handwritten/TransferNativeGhostErasure01.lean', 'project/ShielddSecurity/TransferNativeGhostErasure01.lean']]", "    'handwritten/TransferNativeDeliveryErasure01.lean', 'project/ShielddSecurity/TransferNativeDeliveryErasure01.lean']]")
replace('assert len(records) == 75 and len(audits) == 729', 'assert len(records) == 76 and len(audits) == 733')
replace("'objects': 75", "'objects': 76")
s=s.replace('seventy-five-module','seventy-six-module').replace('729 inherited','733 inherited')
replace("'imports': ['ShielddSecurity.TransferNativeGhostErasure01']", "'imports': ['ShielddSecurity.TransferNativeDeliveryErasure01']")
replace('assert len(names) == 4','assert len(names) == 3')
replace("'fresh_audits': 4", "'fresh_audits': 3")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Exact source Request.step and symbolic entire block walk equality between accepted finite ghost-extended pending encoder and native-only encoder. Actual authenticated reader/current pending getter/body/capability/index callbacks and Config projections reused. Consensus word guard derived from actual request supported width, not a supplied saturation premise. Each successful full source step derives next invariant and canonical bounds through accepted bounded native codec proof; refused steps stop identically. Equality includes failed Option and exact returned parent/deferred queue in every mode and both contexts. One definition/two complete proofs. Supported-only native roundtrip/current initial invariant and bounds/actual canonical inputs/key injection remain explicit. Native-only comparison retains extended object type and observations; symbolic model equality only, not native Rust trace/codec/getter/finite-library/input/callback/ownership/OS closure. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh exact source request step and symbolic whole block walk erasure, deriving next bounded state after each actual successful step. Qualified delivery-erasure four full reports reused with entire 733-report/76-module closure without replay. Historical failures retained; physical/per-run guards unchanged.'"+s[end:]
s=s.replace('SOURCE_BOUNDED_NATIVE_PENDING_GHOST_ERASURE_CAPABILITY_BODY_AND_DELIVERY','SOURCE_BOUNDED_NATIVE_PENDING_GHOST_ERASURE_ACTUAL_STEP_AND_WHOLE_WALK')
s=s.replace('NATIVE_DELIVERY_ERASURE_COMPLETE_SEVENTY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','NATIVE_REACHABLE_ERASURE_COMPLETE_SEVENTY_SIX_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 729", "'inherited_audits': 733")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':3,'inherited_reports':733,'owned_modules':76})
