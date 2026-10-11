"""Seal same whole programs under reachable finite pending codec semantics."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-pending-finite-codec-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-pending-finite-codec-20261011-01'", "CURRENT = DIAG / 'transfer-reachable-pending-block-20261011-01'")
s=s.replace('transfer-pending-finite-codec-checkpoint-20261011-01','transfer-reachable-pending-block-checkpoint-20261011-01')
s=s.replace('pending-finite-codec-endpoint','reachable-pending-block-endpoint')
replace("MODULE = 'TransferPendingFiniteCodec01'", "MODULE = 'TransferReachablePendingBlock01'")
replace('assert len(fresh) == 12','assert len(fresh) == 7')
replace("assert pool['objects'] == 45 and len(pool['inherited_public_reports']) == 440", "assert pool['objects'] == 46 and len(pool['inherited_public_reports']) == 452")
replace("manager_endpoint = DIAG / 'transfer-prepared-accepted-source-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-pending-finite-codec-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-prepared-accepted-source-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-pending-finite-codec-endpoint01.tar.xz'")
replace('beb9cf8125eac5f4b25a008106f2121e451dab1f912be9224446ad4219759d2f','f91d493392a7405f8f1c577ae2732968f55f1c2c35d4acd23cb4a42e8a08bf41')
replace("tar.extractfile('reports/fresh-10-complete-declarations.txt')", "tar.extractfile('reports/fresh-12-complete-declarations.txt')")
replace('assert len(manager_reports) == 10','assert len(manager_reports) == 12')
replace("'module': 'TransferPreparedAcceptedSource01'", "'module': 'TransferPendingFiniteCodec01'")
replace('assert len(combined_reports) == 440','assert len(combined_reports) == 452')
replace('assert len(manager_selected) == 45','assert len(manager_selected) == 46')
replace("reference = {'prepared_accepted_source':", "reference = {'pending_finite_codec':")
replace("'imported_complete_reports': 10", "'imported_complete_reports': 12")
replace("'complete_owned_modules': 45, 'inherited_complete_reports': 440", "'complete_owned_modules': 46, 'inherited_complete_reports': 452")
s=s.replace('Exact forty-five-module whole/current pending/durable reader/source capacity/global block/one-shot seal/source accepted prepare/finite pending codec closure, with 440 original inherited complete reports', 'Exact forty-six-module whole/current pending/durable reader/source capacity/global block/one-shot seal/source accepted prepare/finite pending codec/reachable block closure, with 452 original inherited complete reports')
replace("add(stdout, 'reports/fresh-12-complete-declarations.txt'", "add(stdout, 'reports/fresh-7-complete-declarations.txt'")
replace("add(CURRENT / ('handwritten/' + MODULE + '.lean')", "add(CURRENT / ('generated/' + MODULE + '.lean')")
s=s.replace('finite enum/restoration/erasure/typed codec definitions and seven finite representation/coherent roundtrip/append/freeze/default proofs','maintained generated same whole step/walk/freeze and finite codec wrapper; one full facts definition and six reachable coherence proofs')
s=s.replace('complete forty-five-module first import root','complete forty-six-module first import root')
s=s.replace('verified 440 inherited reports','verified 452 inherited reports')
s=s.replace('FINITE_PENDING_ENUM_ERASURE_GHOST_AND_REACHABLE_COHERENT_CODEC_QUALIFIED','WHOLE_REACHABLE_PENDING_CODEC_BLOCK_FREEZE_WITH_FINITE_ENUM_GHOST_QUALIFIED')
replace("'fresh_definition_audits': 5", "'fresh_definition_audits': 1")
replace("'fresh_theorem_audits': 7", "'fresh_theorem_audits': 6")
replace("'fresh_complete_public_audits': 12", "'fresh_complete_public_audits': 7")
replace("'inherited_complete_public_audits': 440", "'inherited_complete_public_audits': 452")
anchor="mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())"; assert s.count(anchor)==1
extra="""regeneration = json.loads((CURRENT / 'regeneration.json').read_bytes())
assert regeneration['byte_exact'] and pin(regeneration['generated']['path']) == regeneration['generated']
assert pin(regeneration['independent_regeneration']['path']) == regeneration['independent_regeneration']
assert Path(regeneration['generated']['path']).read_bytes() == Path(regeneration['independent_regeneration']['path']).read_bytes()
for name in ['generate.py', 'regeneration.json']:
    assert pin(CURRENT / name) in plan['pins']
    add(CURRENT / name, 'qualified/' + name, 'maintained generation and byte-exact independent regeneration')
add(regeneration['independent_regeneration']['path'], 'regeneration/TransferReachablePendingBlock01.lean', 'independent byte-exact generated proof source; zero duplicate kernel credit')
"""
s=s.replace(anchor,extra+anchor)
start=s.index("    'scope': mapping['scope'] + "); end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' All seven declarations have original complete type/axiom reports. Same whole programs derive coherent states before restricted codec use; finite enum default initialization and reconstructed Sealed ghost membership yield exact block/freeze/refusal facts without any arbitrary-Pending roundtrip assumption. Native collection/typed embedding/value/ownership/phase/durability remain explicit. No native/control/full certification credit.'}"+s[end:]
s=s.replace("'fresh_audits': 12, 'inherited_audits': 440", "'fresh_audits': 7, 'inherited_audits': 452")
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':7,'inherited_reports':452,'owned_modules':46})
