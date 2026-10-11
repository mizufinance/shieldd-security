"""Derive a strict readback sealer for current-count refusal; never replay ancestors."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent
DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-ordinary-index-read-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
s=s.replace('transfer-ordinary-index-read-20261011-01','transfer-ordinary-index-count-20261011-01')
s=s.replace('transfer-ordinary-index-read-checkpoint','transfer-ordinary-index-count-checkpoint')
s=s.replace('ordinary-index-read-endpoint','ordinary-index-count-endpoint')
replace("MODULE = 'TransferOrdinaryIndexReadSource01'", "MODULE = 'TransferOrdinaryIndexCountSource01'")
replace('assert len(fresh) == 7','assert len(fresh) == 6')
replace("assert pool['objects'] == 20 and len(pool['inherited_public_reports']) == 243", "assert pool['objects'] == 21 and len(pool['inherited_public_reports']) == 250")
replace("manager_endpoint = DIAG / 'transfer-volume-height-keys-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-ordinary-index-read-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-volume-height-keys-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-ordinary-index-read-endpoint01.tar.xz'")
replace('0ed073e4bc92c301bda4449c38092e490ae399db16f010b87abf9cff4ab163b6','5e8bc8455d9883427714d79fcba60857a5c7d95e8a515647d54ef677d0ae82e3')
replace("tar.extractfile('reports/fresh-9-complete-declarations.txt')", "tar.extractfile('reports/fresh-7-complete-declarations.txt')")
replace('assert len(manager_reports) == 9','assert len(manager_reports) == 7')
replace("'module': 'TransferVolumeHeightKeys01'", "'module': 'TransferOrdinaryIndexReadSource01'")
replace('assert len(combined_reports) == 243','assert len(combined_reports) == 250')
replace('assert len(manager_selected) == 20','assert len(manager_selected) == 21')
replace("reference = {'source_keys':", "reference = {'current_index_reads':")
replace("'imported_complete_reports': 9},", "'imported_complete_reports': 7},")
replace("'complete_owned_modules': 20, 'inherited_complete_reports': 243", "'complete_owned_modules': 21, 'inherited_complete_reports': 250")
replace('Exact twenty-module closure through source ASCII volume/height keys and whole indexed success, with all 243 inherited complete reports.', 'Exact twenty-one-module closure through actual current NV reads and whole Ordinary duplicate refusal, with all 250 inherited complete reports.')
s=s.replace('two current-overlay NV read/backend definitions and five finite read/duplicate/whole-delivery refusal proofs','six finite current-count/semantic-decode/semantic-overflow/whole-delivery refusal proofs')
replace("add(stdout, 'reports/fresh-7-complete-declarations.txt'", "add(stdout, 'reports/fresh-6-complete-declarations.txt'")
s=s.replace('complete twenty-module first import root','complete twenty-one-module first import root')
s=s.replace('verified 243 inherited reports','verified 250 inherited reports')
s=s.replace('CURRENT_OVERLAY_INDEX_READ_DERIVES_EXISTING_PARENT_ID_WHOLE_ORDINARY_DELIVERY_REFUSAL_QUALIFIED','CURRENT_OVERLAY_COUNT_DERIVES_MALFORMED_OR_OVERFLOW_WHOLE_ORDINARY_DELIVERY_REFUSAL_QUALIFIED')
replace("'fresh_definition_audits': 2, 'fresh_theorem_audits': 5", "'fresh_definition_audits': 0, 'fresh_theorem_audits': 6")
replace("'fresh_complete_public_audits': 7", "'fresh_complete_public_audits': 6")
replace("'inherited_complete_public_audits': 243", "'inherited_complete_public_audits': 250")
start=s.index("    'scope': mapping['scope'] + ")
end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"""    'scope': mapping['scope'] + ' Six handwritten theorems qualified in one guarded attempt. Semantic decode/overflow conclusions require successful preceding actual modeled observations. Generic malformed/saturated-count refusal holds for all conversion, extractor, body and read-availability outcomes. Unavailable read or earlier error cannot count as a runtime semantic control. No native control, Rust correspondence or durable-publication evidence.'}
""".rstrip()+s[end:]
s=s.replace("'fresh_audits': 7", "'fresh_audits': 6").replace("'inherited_audits': 243", "'inherited_audits': 250")
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':6,'inherited_reports':250,'owned_modules':21})
