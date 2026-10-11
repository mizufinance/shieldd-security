"""Derive fresh inspection packet assembly from the exact previously sealed producer."""
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-index-writer-endpoint-20261011-01/assemble.py'
assert not (ROOT / 'assemble.py').exists()
# The source is also carried byte-for-byte by the verified predecessor archive.
import tarfile
archive = OLD.parent / 'portable-windows-index-writer-endpoint01.tar.xz'
assert hashlib.sha256(archive.read_bytes()).hexdigest() == '791d8ac33050913aed3d68aaae3399a809b3565e2d8274bf8708409cac9928b2'
with tarfile.open(archive, 'r:xz') as tar:
    assert tar.extractfile('assemble.py').read() == OLD.read_bytes()
source = OLD.read_text()
replacements = [
    ('transfer-index-writer-model-20261011-', 'transfer-index-inspection-20261011-'),
    ('transfer-index-writer-checkpoint-20261011-', 'transfer-index-inspection-checkpoint-20261011-'),
    ('portable-windows-index-writer-endpoint01.tar.xz', 'portable-windows-index-inspection-endpoint01.tar.xz'),
    ('TransferIndexWriterModel01', 'TransferIndexInspectionFacts01'),
    ('assert len(fresh) == 26', 'assert len(fresh) == 16'),
    ("pool['objects'] == 3 and len(pool['inherited_public_reports']) == 33", "pool['objects'] == 4 and len(pool['inherited_public_reports']) == 59"),
    ("'reports/fresh-26-complete-declarations.txt'", "'reports/fresh-16-complete-declarations.txt'"),
    ('14 definition/structure and 12 theorem full types and standard axioms', '4 definition and 12 theorem full types and standard axioms'),
    ('handwritten finite three-write model and raw success frame', 'handwritten finite inspection inversion, byte suffix separation and exact values'),
    ('complete exact three-module first owned import root', 'complete exact four-module first owned import root'),
    ('original syntax and proof elaboration failure', 'original two case-reduced proof-goal elaboration errors'),
    ("'THREE_NONVERIFIABLE_INDEX_WRITES_AND_PRIOR_RAW_EFFECT_FRAME_QUALIFIED'", "'SUCCESSFUL_INDEX_OBSERVATIONS_CHECKED_INCREMENT_BYTE_TAG_SEPARATION_AND_VALUES_QUALIFIED'"),
    ("'fresh_definition_audits': 14", "'fresh_definition_audits': 4"),
    ("'fresh_complete_public_audits': 26", "'fresh_complete_public_audits': 16"),
    ("'inherited_complete_public_audits': 33", "'inherited_complete_public_audits': 59"),
    ("'fresh_audits': 26", "'fresh_audits': 16"),
    ("'inherited_audits': 33", "'inherited_audits': 59"),
    ("'schema': 'transfer-index-writer-endpoint-v1'", "'schema': 'transfer-index-inspection-endpoint-v1'")]
for before, after in replacements:
    assert before in source, before
    source = source.replace(before, after)
start = source.index('with tarfile.open(raw_archive,')
end = source.index("(ROOT / 'inherited-reference.json')", start)
source = source[:start] + '''index_root = DIAG / 'transfer-index-writer-endpoint-20261011-01'
index_archive = index_root / 'portable-windows-index-writer-endpoint01.tar.xz'
assert pin(index_archive)['sha256'] == '791d8ac33050913aed3d68aaae3399a809b3565e2d8274bf8708409cac9928b2'
with tarfile.open(raw_archive, 'r:xz') as raw_tar, tarfile.open(delivery_archive, 'r:xz') as delivery_tar, tarfile.open(index_archive, 'r:xz') as index_tar:
    for selected in pool['selected']:
        if selected['module'] == 'TransferIndexWriterModel01':
            tar = index_tar
        elif selected['module'] == 'TransferRawDeliveryComposition01':
            tar = delivery_tar
        else:
            tar = raw_tar
        assert tar.extractfile('source/ShielddSecurity/' + selected['module'] + '.lean').read() == Path(selected['source']['path']).read_bytes()
    raw_review = json.loads(raw_tar.extractfile('review.json').read())
    delivery_review = json.loads(delivery_tar.extractfile('review.json').read())
    index_review = json.loads(index_tar.extractfile('review.json').read())
    assert {**raw_review['fresh_audits'], **raw_review['inherited_audits'], **delivery_review['fresh_audits'], **index_review['fresh_audits']} == pool['inherited_public_reports']
reference = {'raw': {'accepted_evidence_commit': 'ae307b2af3c98242cc6a3be82e5673d89b54f9c4', 'archive': pin(raw_archive), 'manifest': pin(RAW / 'manifest.json')},
    'delivery': {'accepted_evidence_commit': '95a570eeab095a08374e6b2a0e850be31330fc21', 'archive': pin(delivery_archive), 'manifest': pin(DELIVERY / 'manifest.json')},
    'index': {'status': 'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE', 'archive': pin(index_archive), 'manifest': pin(index_root / 'manifest.json')},
    'inherited_complete_declarations': 59, 'inherited_sources': 4,
    'external_floor_reference': 'raw archive: context/core-floor-reference.json, accepted exact complete core floor at queue evidence 7f4abf584595911545bd8a7645e487c629931cba',
    'all_inherited_source_and_report_identities_verified': True}
''' + source[end:]
old_scope = source.index("'scope': mapping['scope'] + '")
scope_end = source.index("'}\n(ROOT / 'review.json')", old_scope)
source = source[:old_scope] + "'scope': mapping['scope'] + ' Inspection success recovers actual conversion, absent-ID observation, count read/decode and checked successor; next=ordinal+1 is derived and bounded below 2^64. ASCII /count, /entry/ and /id/ suffix separation is proved for arbitrary shared prefixes and appended values. Under the explicitly equality-preserving Nat projection, exact entry payload, identifier ordinal and next count writes follow from successful inspection. Conversion, duplicate and overflow refusals derive their intended model error; these proofs are not runtime negative controls. The original failed source remains zero credit.'" + source[scope_end+1:]
# Replace the old title and include this exact derivation source in the new archive.
source = source.replace(source.splitlines()[0], '\"\"\"Seal inspection facts with exact inherited source/report/guard references.\"\"\"')
source = source.replace("add(Path(__file__), 'assemble.py', 'transport assembly source')", "add(ROOT / 'prepare_assembly.py', 'prepare_assembly.py', 'exact fresh assembly derivation source')\nadd(Path(__file__), 'assemble.py', 'transport assembly source')")
assert "'fresh_audits': 26" not in source and "'inherited_audits': 33" not in source
(ROOT / 'assemble.py').write_text(source)
print({'assembly_bytes': (ROOT / 'assemble.py').stat().st_size})
