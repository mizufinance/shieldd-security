"""Derive current-overlay refusal packet from the sealed cache framing carrier."""
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
assert not (ROOT / 'assemble.py').exists()
source = (DIAG / 'transfer-raw-source-frames-endpoint-20261011-01/assemble.py').read_text()
def replace(before, after):
    global source
    assert source.count(before) == 1, before
    source = source.replace(before, after)

source = source.replace('transfer-raw-source-frames-20261011-02', 'transfer-current-volume-source-20261011-02')
source = source.replace('transfer-raw-source-frames-checkpoint', 'transfer-current-volume-checkpoint')
source = source.replace('raw-source-frames-endpoint', 'current-volume-endpoint')
replace("MODULE = 'TransferRawSourceFrames01'", "MODULE = 'TransferCurrentVolumeSource01'")
replace('assert len(fresh) == 7', 'assert len(fresh) == 9')
replace("assert pool['objects'] == 7 and len(pool['inherited_public_reports']) == 110", "assert pool['objects'] == 8 and len(pool['inherited_public_reports']) == 117")
replace("manager_endpoint = DIAG / 'transfer-sct-insertion-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-raw-source-frames-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-sct-insertion-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-raw-source-frames-endpoint01.tar.xz'")
replace('2ed851ce4a03ed94cf1d506bb689a4ddc229e3d69fb9701ac37529aa59c05852', '3623e7b32a7fb61bae9bfb85408e9686d0901361d3de6b16fc36b1220c9a32af')
replace("tar.extractfile('reports/fresh-13-complete-declarations.txt')", "tar.extractfile('reports/fresh-7-complete-declarations.txt')")
replace('assert len(manager_reports) == 13', 'assert len(manager_reports) == 7')
replace("'module': 'TransferSctInsertionSource01'", "'module': 'TransferRawSourceFrames01'")
start = source.index("    if selected['module'] == 'TransferSctInsertionSource01':")
end = source.index('    assert pin(carrier[\'path\']) == carrier', start)
source = source[:start] + """    if selected['module'] == 'TransferRawSourceFrames01':
        carrier = pin(manager_archive)
    elif selected['module'] == 'TransferSctInsertionSource01':
        carrier = manager_reference['sct']['archive']
    elif selected['module'] == 'TransferNoteManagerSource01':
        carrier = manager_reference['ancestors']['manager']['archive']
    else:
        tag = {'TransferStateDelta': 'raw', 'TransferRawStateProgram01': 'raw',
            'TransferNullifierReaderVector01': 'vector', 'TransferNullifierBatchSource01': 'batch',
            'TransferRawEffectsSource01': 'effects'}[selected['module']]
        carrier = manager_reference['ancestors']['ancestors'][tag]['archive']
""" + source[end:]
replace("assert manager_reference['ancestors']['core_floor']['original'] == plan['external_floor']", "assert manager_reference['ancestors']['ancestors']['core_floor']['original'] == plan['external_floor']")
replace("reference = {'sct':", "reference = {'framing':")
source = source.replace("'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE'", "'PARENT_REVIEW_ACCEPTED_AND_PUBLISHED_f6b0a8c5e1df4d2188d1f5e6ae31e9b3973ce822'")
source = source.replace("'imported_complete_reports': 13", "'imported_complete_reports': 7")
source = source.replace("'complete_owned_modules': 7", "'complete_owned_modules': 8")
source = source.replace("'inherited_complete_reports': 110", "'inherited_complete_reports': 117")
source = source.replace('Exact cache/raw/vector/batch/raw-effect/manager/SCT closure;', 'Exact cache/raw/vector/batch/raw-effect/manager/SCT/framing closure;')
source = source.replace('one callback installation definition and six symbolic all-return cache domain proofs', 'four current-overlay executable definitions and five finite source-derived refusal proofs')
source = source.replace('reports/fresh-7-complete-declarations.txt\', \'all raw', 'reports/fresh-9-complete-declarations.txt\', \'all raw')
source = source.replace('complete seven-module first import root', 'complete eight-module first import root')
source = source.replace('verified 110 inherited reports', 'verified 117 inherited reports')
source = source.replace('transfer-raw-source-frames-20261011-01', 'transfer-current-volume-source-20261011-01')
source = source.replace('preserved original proof reduction/parser rejection', 'preserved original proof reduction rejection')
source = source.replace('exact pinned SCT cache/capacity/insert source; semantic interfaces explicit', 'exact pinned current volume get_raw and layered cache source; semantic interfaces explicit')
source = source.replace('DERIVED_ALL_RETURN_NOTE_RESHAPE_AND_FEE_FUNDING_VERIFIABLE_NONVERIFIABLE_CACHE_FRAMES_QUALIFIED', 'SOURCE_DERIVED_CURRENT_OVERLAY_ORDINARY_REFUSAL_AND_DELIVERY_PRESERVATION_QUALIFIED')
source = source.replace("'fresh_definition_audits': 1, 'fresh_theorem_audits': 6", "'fresh_definition_audits': 4, 'fresh_theorem_audits': 5")
source = source.replace("'fresh_complete_public_audits': 7", "'fresh_complete_public_audits': 9")
source = source.replace("'inherited_complete_public_audits': 110", "'inherited_complete_public_audits': 117")
start = source.index("    'scope': mapping['scope'] + ")
end = source.index("\ndump(ROOT / 'review.json', review)", start)
source = source[:start] + """    'pre_admission_refused_cli': {'supplied_sha256': '00000000', 'lean_started': False, 'proof_credit': 0},
    'scope': mapping['scope'] + ' All four executable definitions and original refusal contracts are unchanged from the rejected attempt; the successor adds a small volume-tail lemma and stages rewrite observations before unfolding callback aliases. No successful reshape, desired read flag or rollback cache is a premise. Read errors remain distinct from absence and any present bytes imply spent. Original failed Lean and pre-admission invalid CLI receive zero credit.'}
""".rstrip() + source[end:]
source = source.replace("'fresh_audits': 7", "'fresh_audits': 9").replace("'inherited_audits': 110", "'inherited_audits': 117")
(ROOT / 'assemble.py').write_text(source)
print({'fresh_reports': 9, 'inherited_reports': 117, 'owned_modules': 8})
