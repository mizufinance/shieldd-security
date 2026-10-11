"""Seal exact generated record read bound with independent regeneration."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-durable-write-source-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-durable-write-source-20261011-01'", "CURRENT = DIAG / 'transfer-record-read-bound-20261011-01'")
s=s.replace('transfer-durable-write-source-checkpoint-20261011-01','transfer-record-read-bound-checkpoint-20261011-01')
s=s.replace('durable-write-source-endpoint','record-read-bound-endpoint')
replace("MODULE = 'TransferDurableWriteSource01'", "MODULE = 'TransferRecordReadBound01'")
replace("assert pool['objects'] == 58 and len(pool['inherited_public_reports']) == 576", "assert pool['objects'] == 59 and len(pool['inherited_public_reports']) == 584")
replace("manager_endpoint = DIAG / 'transfer-writer-recovery-join-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-durable-write-source-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-writer-recovery-join-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-durable-write-source-endpoint01.tar.xz'")
s=s.replace('334ccfbfa9bbf867f4ee909df762fbca06052f7cf641a992167bb6b74f418223','e682cd778fb913b6af1d63db8d7aec3116ba638b655caa57d5326f6d0224d380')
replace("tar.extractfile('reports/fresh-6-complete-declarations.txt')", "tar.extractfile('reports/fresh-8-complete-declarations.txt')")
replace('assert len(manager_reports) == 6','assert len(manager_reports) == 8')
replace("'module': 'TransferWriterRecoveryJoin01'", "'module': 'TransferDurableWriteSource01'")
replace('assert len(combined_reports) == 576','assert len(combined_reports) == 584')
replace('assert len(manager_selected) == 58','assert len(manager_selected) == 59')
replace("reference = {'writer_recovery_join':", "reference = {'durable_write_source':")
replace("'imported_complete_reports': 6", "'imported_complete_reports': 8")
replace("'complete_owned_modules': 58, 'inherited_complete_reports': 576", "'complete_owned_modules': 59, 'inherited_complete_reports': 584")
s=s.replace('Exact fifty-eight-module','Exact fifty-nine-module').replace('with 576 original inherited','with 584 original inherited')
replace("CURRENT / ('handwritten/' + MODULE + '.lean')", "CURRENT / ('generated/' + MODULE + '.lean')")
s=s.replace('source file operation observation/durable write/intent writer installation definitions and four source success/missing-parent/directory-failure/intent-refusal proofs','generated exact source byte cap/take limit/read callback and returned-length/error/oversize proofs')
s=s.replace('complete fifty-eight-module first import root','complete fifty-nine-module first import root').replace('verified 576 inherited reports','verified 584 inherited reports')
s=s.replace('SOURCE_DURABLE_FILE_WRITE_ORDER_OBSERVED_PROGRESS_AND_INTENT_FAILURE_QUALIFIED','SOURCE_RECORD_READ_TAKE_LIMIT_RETURNED_BYTE_BOUND_AND_REFUSALS_QUALIFIED')
replace("'inherited_complete_public_audits': 576", "'inherited_complete_public_audits': 584")
assert s.count("'fresh_audits': 8, 'inherited_audits': 576") == 2
s=s.replace("'fresh_audits': 8, 'inherited_audits': 576", "'fresh_audits': 8, 'inherited_audits': 584")
anchor="add(stdout, 'reports/fresh-8-complete-declarations.txt'"
i=s.index(anchor)
s=s[:i]+"regenerated = DIAG / 'transfer-record-read-regeneration-20261011-01'\nassert (regenerated / 'generated' / (MODULE + '.lean')).read_bytes() == (CURRENT / 'generated' / (MODULE + '.lean')).read_bytes()\nfor path, name in [(CURRENT / 'generate.py', 'generator/generate.py'), (CURRENT / 'generation.json', 'generator/generation.json'), (regenerated / 'generation.json', 'regeneration/generation.json'), (regenerated / 'generated' / (MODULE + '.lean'), 'regeneration/' + MODULE + '.lean')]:\n    assert pin(path) in plan['pins']\n    add(path, name, 'maintained source generator and byte-identical independent regeneration; no generated hand edit')\n"+s[i:]
start=s.index("    'scope': mapping['scope'] + "); end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' All eight declarations retain original complete type/axiom reports. Source bounded read success derives actual callback bytes and checked size; unavailable reads and oversized observed bytes refuse. Native Read/Take allocation, partial consumption, serde, OS, owner and representation remain explicit interfaces. Zero native/control/full certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':8,'inherited_reports':584,'owned_modules':59})
