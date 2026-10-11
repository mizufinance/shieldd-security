"""Seal bounded source request/block-walk erasure and failed heap attempts."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-native-delivery-erasure-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-native-delivery-erasure-20261011-01'", "CURRENT = DIAG / 'transfer-native-reachable-erasure-20261011-03'")
s=s.replace('transfer-native-delivery-erasure-checkpoint-20261011-01','transfer-native-reachable-erasure-checkpoint-20261011-03').replace('native-delivery-erasure-endpoint','native-reachable-erasure-endpoint')
replace("MODULE = 'TransferNativeDeliveryErasure01'", "MODULE = 'TransferNativeReachableErasure01'")
replace("assert pool['objects'] == 75 and len(pool['inherited_public_reports']) == 729", "assert pool['objects'] == 76 and len(pool['inherited_public_reports']) == 733")
replace("manager_endpoint = DIAG / 'transfer-native-ghost-erasure-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-native-delivery-erasure-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-native-ghost-erasure-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-native-delivery-erasure-endpoint01.tar.xz'")
replace('cb1fc96e7dc67da608aa70a37f3b9a0ed466782cf4ebaec4bf49142616be90b0','a58c8d7905d47f6c52f257193883d6e54ab6ff788d600a448ddda8aa1b3331ae')
replace("tar.extractfile('reports/fresh-5-complete-declarations.txt')", "tar.extractfile('reports/fresh-4-complete-declarations.txt')")
replace('assert len(manager_reports) == 5','assert len(manager_reports) == 4')
replace("'module': 'TransferNativeGhostErasure01'", "'module': 'TransferNativeDeliveryErasure01'")
replace('assert len(combined_reports) == 729','assert len(combined_reports) == 733')
replace('assert len(manager_selected) == 75','assert len(manager_selected) == 76')
replace("reference = {'native_ghost_erasure':", "reference = {'native_delivery_erasure':")
replace("'imported_complete_reports': 5", "'imported_complete_reports': 4")
replace("'complete_owned_modules': 75, 'inherited_complete_reports': 729", "'complete_owned_modules': 76, 'inherited_complete_reports': 733")
s=s.replace('seventy-five-module','seventy-six-module').replace('729 original inherited','733 original inherited').replace('verified 729 inherited','verified 733 inherited')
replace("'fresh_definition_audits': 0", "'fresh_definition_audits': 1")
replace("'fresh_theorem_audits': 4", "'fresh_theorem_audits': 3")
replace("'inherited_complete_public_audits': 729", "'inherited_complete_public_audits': 733")
replace("'fresh_audits': 4, 'inherited_audits': 729", "'fresh_audits': 4, 'inherited_audits': 733",2)
replace('SOURCE_BOUNDED_CANONICAL_PENDING_CAPABILITY_BODY_AND_EXACT_DELIVERY_ERASURE_QUALIFIED','SOURCE_BOUNDED_CANONICAL_PENDING_ACTUAL_REQUEST_AND_WHOLE_WALK_ERASURE_QUALIFIED')
replace("'rejected_attempts': 0", "'rejected_attempts': 2")
anchor="add(stdout, 'reports/fresh-4-complete-declarations.txt'";i=s.index(anchor)
extra="""for suffix in ['01','02']:
    failed=DIAG/('transfer-native-reachable-erasure-20261011-'+suffix)
    failed_events=[json.loads(line) for line in (failed/'events.jsonl').read_text().splitlines()]
    assert len(failed_events)==2 and failed_events[-1]['result']['status']=='failed'
    for name in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferNativeReachableErasure01.lean','project/ShielddSecurity/TransferNativeReachableErasure01.lean','runs/01-TransferNativeReachableErasure01/stdout.txt']:
        assert pin(failed/name) in plan['pins']
        add(failed/name,'rejected/source'+suffix+'/'+name,'strict failed kernel heap attempt; source01 also head-membership application error. Original whole0/no semantic control credit, all guards unchanged')
"""
s=s[:i]+extra+s[i:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' One definition/three original complete proof reports retained. Actual full Request step and symbolic entire bounded block walk compare encoder selection with SAME ExtendedObject type, decoder and callbacks. Small returned-value Option bind lemma avoids full model expansion; next invariant/bounds derived from original successful source step. Original step/walk contracts unchanged; helper audited separately. Failed01/02 heap attempts retained with zero whole-proof/control credit, fixed heap unchanged. No native Rust trace/codec/getter/input closure. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':4,'inherited_reports':733,'owned_modules':76,'rejected_attempts':2})
