"""Seal canonical finite native codec and explicit superseded byte-only run."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-global-commit-join-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-global-commit-join-20261011-01'", "CURRENT = DIAG / 'transfer-bounded-native-codec-20261011-02'")
s=s.replace('transfer-global-commit-join-checkpoint-20261011-01','transfer-bounded-native-codec-checkpoint-20261011-02').replace('global-commit-join-endpoint','bounded-native-codec-endpoint')
replace("MODULE = 'TransferGlobalCommitJoin01'", "MODULE = 'TransferBoundedNativeCodec01'")
replace('assert len(fresh) == 5','assert len(fresh) == 14')
replace("assert pool['objects'] == 69 and len(pool['inherited_public_reports']) == 696", "assert pool['objects'] == 70 and len(pool['inherited_public_reports']) == 701")
replace("manager_endpoint = DIAG / 'transfer-end-to-end-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-global-commit-join-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-end-to-end-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-global-commit-join-endpoint01.tar.xz'")
replace('7d38251e6c29af8105930c8f5d5ac46a3887ff3afa870d1a4e0d29cd03ad5eab','6a5c3091b3722f2bb807d5da24c0c32597f5d1bf745eeb061f7dcca069d03d5c')
replace("tar.extractfile('reports/fresh-13-complete-declarations.txt')", "tar.extractfile('reports/fresh-5-complete-declarations.txt')")
replace('assert len(manager_reports) == 13','assert len(manager_reports) == 5')
replace("'module': 'TransferEndToEnd01'", "'module': 'TransferGlobalCommitJoin01'")
replace('assert len(combined_reports) == 696','assert len(combined_reports) == 701')
replace('assert len(manager_selected) == 69','assert len(manager_selected) == 70')
replace("reference = {'end_to_end':", "reference = {'global_commit_join':")
replace("'imported_complete_reports': 13", "'imported_complete_reports': 5")
replace("'complete_owned_modules': 69, 'inherited_complete_reports': 696", "'complete_owned_modules': 70, 'inherited_complete_reports': 701")
s=s.replace('sixty-nine-module','seventy-module').replace('696 original inherited','701 original inherited').replace('verified 696 inherited','verified 701 inherited')
replace("add(stdout, 'reports/fresh-5-complete-declarations.txt'", "add(stdout, 'reports/fresh-14-complete-declarations.txt'")
replace("'fresh_definition_audits': 2", "'fresh_definition_audits': 6")
replace("'fresh_theorem_audits': 3", "'fresh_theorem_audits': 8")
replace("'fresh_complete_public_audits': 5", "'fresh_complete_public_audits': 14")
replace("'inherited_complete_public_audits': 696", "'inherited_complete_public_audits': 701")
replace("'fresh_audits': 5, 'inherited_audits': 696", "'fresh_audits': 14, 'inherited_audits': 701",2)
replace('SOURCE_WHOLE_GLOBAL_INPUTS_TO_HOST_PUBLICATION_UNDER_FINITE_CODEC_AND_FINALIZATION_FIELD_CONTRACT_QUALIFIED','SOURCE_REACHABLE_CANONICAL_FIELD_NATIVE_CODEC_AND_BOUNDED_WHOLE_PUBLICATION_CAPSTONE_QUALIFIED')
anchor="add(stdout, 'reports/fresh-14-complete-declarations.txt'";i=s.index(anchor)
extra="""superseded = DIAG/'transfer-bounded-native-codec-20261011-01'
superseded_events = [json.loads(line) for line in (superseded/'events.jsonl').read_text().splitlines()]
assert len(superseded_events)==2 and superseded_events[-1]['result']['status']=='passed'
superseded_plan=json.loads((superseded/'plan.json').read_bytes())
superseded_audits=m.audit((superseded/'runs/01-TransferBoundedNativeCodec01/stdout.txt').read_text(),superseded_plan['targets'][0]['audit_names'])
assert len(superseded_audits)==13 and superseded_audits==superseded_events[-1]['result']['audits']
for name in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferBoundedNativeCodec01.lean','project/ShielddSecurity/TransferBoundedNativeCodec01.lean','runs/01-TransferBoundedNativeCodec01/stdout.txt']:
    assert pin(superseded/name) in plan['pins']
    add(superseded/name,'superseded/byte-only01/'+name,'strict passed abstract byte-only13, unpublished and unselected; canonical domain intentionally narrowed in source02; no native credit')
for obj in superseded_events[-1]['result']['objects']:
    assert pin(obj['path'])==obj
    assert obj not in [r['object'] for r in pool['selected']]
for name in ['context/canonical-domain.json','context/runtime-library/jubjub-0.10.0-lib.rs','context/runtime-library/bls12_381-0.8.0-scalar.rs','context/runtime-library/source-copy.json','prepare_recipe_count_failure.py']:
    assert pin(CURRENT/name) in plan['pins']
    add(CURRENT/name,'qualified/'+name,'exact canonical Nullifier/Jubjub Fq/BLS Scalar source alias/modulus copies and stopped preparation count assertion; no semantic or control credit')
domain=json.loads((CURRENT/'context/canonical-domain.json').read_bytes())
assert domain['modulus']=='52435875175126190479447740508185965837690552500527637822603658699938581184513'
assert pin(domain['math_source']['path'])==domain['math_source'] and domain['math_source'] in plan['pins']
add(domain['math_source']['path'],'context/shared-mathematical-field/Scalar.lean','same accepted actual field modulus, source identity only; no mathematical replay')
"""
s=s[:i]+extra+s[i:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' All fourteen complete original full types/axioms retained. Native codec obligation only canonical shared-field finite values at consensus capacity. Unsupported totalization is proof-only; symbolic bounded source walk proves actual pending encodings stored in native sum branch. Superseded byte-only01 strict passed13 retained entirely but no selected fresh/kernel/native credit. Source02 intentionally narrows declarations/premises/conclusions; no ancestor or field replay. Native embedding/field-byte/finite library/other-object/actual-trace/finalization/snapshot/ICS23/temporal/partition/ownership/OS remain interfaces. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':14,'inherited_reports':701,'owned_modules':70,'superseded_unselected_byte_only_reports':13,'rejected_attempts':0})
