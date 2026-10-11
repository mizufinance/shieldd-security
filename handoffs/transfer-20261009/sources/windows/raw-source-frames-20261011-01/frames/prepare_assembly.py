"""Derive lossless all-return cache framing packet from SCT packet recipe."""
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
BASE = DIAG / 'transfer-sct-insertion-endpoint-20261011-01/assemble.py'
assert not (ROOT / 'assemble.py').exists() and not (ROOT / 'manifest.json').exists()
source = BASE.read_text()

def replace(before, after):
    global source
    assert source.count(before) == 1, before
    source = source.replace(before, after)

source = source.replace('transfer-sct-insertion-source-20261011-01', 'transfer-raw-source-frames-20261011-02')
source = source.replace('transfer-sct-insertion-checkpoint', 'transfer-raw-source-frames-checkpoint')
source = source.replace('sct-insertion-endpoint', 'raw-source-frames-endpoint')
source = source.replace("MODULE = 'TransferSctInsertionSource01'", "MODULE = 'TransferRawSourceFrames01'")
source = source.replace('fresh-13-complete-declarations', 'fresh-7-complete-declarations')
replace('assert len(fresh) == 13', 'assert len(fresh) == 7')
replace("assert pool['objects'] == 6 and len(pool['inherited_public_reports']) == 97",
    "assert pool['objects'] == 7 and len(pool['inherited_public_reports']) == 110")
# Use the actual SCT module as the immediate source/report carrier.
source = source.replace("manager_endpoint = DIAG / 'transfer-note-manager-endpoint-20261011-01'",
    "manager_endpoint = DIAG / 'transfer-sct-insertion-endpoint-20261011-01'")
source = source.replace("manager_archive = manager_endpoint / 'portable-windows-note-manager-endpoint01.tar.xz'",
    "manager_archive = manager_endpoint / 'portable-windows-sct-insertion-endpoint01.tar.xz'")
source = source.replace('669cb795b7221dbcffd6ecf0c6eaf663f6fe71eca86cba8a4f8708dd38ccfc1f',
    '2ed851ce4a03ed94cf1d506bb689a4ddc229e3d69fb9701ac37529aa59c05852')
source = source.replace("tar.extractfile('reports/fresh-7-complete-declarations.txt')",
    "tar.extractfile('reports/fresh-13-complete-declarations.txt')")
replace("'module': 'TransferNoteManagerSource01'", "'module': 'TransferSctInsertionSource01'")
replace("if selected['module'] == 'TransferNoteManagerSource01':", "if selected['module'] == 'TransferSctInsertionSource01':")
replace("carrier = manager_reference[tag]['archive']",
    "carrier = manager_reference['manager']['archive'] if selected['module'] == 'TransferNoteManagerSource01' else manager_reference['ancestors'][tag]['archive']")
replace("'TransferNullifierReaderVector01': 'vector', 'TransferNullifierBatchSource01': 'batch', 'TransferRawEffectsSource01': 'effects'}[selected['module']]",
    "'TransferNullifierReaderVector01': 'vector', 'TransferNullifierBatchSource01': 'batch', 'TransferRawEffectsSource01': 'effects', 'TransferNoteManagerSource01': 'manager'}[selected['module']]")
replace("assert manager_reference['core_floor']['original'] == plan['external_floor']",
    "assert manager_reference['ancestors']['core_floor']['original'] == plan['external_floor']")
source = source.replace("'complete_owned_modules': 6", "'complete_owned_modules': 7")
source = source.replace("'inherited_complete_reports': 97", "'inherited_complete_reports': 110")
source = source.replace("'manager': {'archive': pin(manager_archive)", "'sct': {'archive': pin(manager_archive)")
source = source.replace("'PARENT_REVIEW_ACCEPTED; PUBLICATION_SEPARATE'", "'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE'")
source = source.replace('Exact cache/raw/vector/batch/raw-effect/manager closure;',
    'Exact cache/raw/vector/batch/raw-effect/manager/SCT closure;')
replace("for name in ['prepare.py', 'prepare_recipe.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:",
    "for name in ['prepare.py', 'prepare_successor.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:")
source = source.replace('five definitions and eight finite source/cache/event proofs',
    'one callback installation definition and six symbolic all-return cache domain proofs')
source = source.replace('complete six-module first import root', 'complete seven-module first import root')
source = source.replace('verified 97 inherited reports', 'verified 110 inherited reports')
replace("for name in ['preservation_check.py', 'preservation.json']:",
    """old = DIAG / 'transfer-raw-source-frames-20261011-01'
old_events = [json.loads(s) for s in (old / 'events.jsonl').read_text().splitlines()]
assert len(old_events) == 2 and old_events[-1]['result']['status'] == 'failed'
for name in ['prepare.py', 'prepare_recipe.py', 'plan.json', 'events.jsonl']:
    add(old / name, 'rejected/' + name, 'preserved original proof reduction/parser rejection; zero credit')
add(old / ('handwritten/' + MODULE + '.lean'), 'rejected/source.lean', 'exact original rejected proof source')
add(old / ('runs/01-' + MODULE + '/stdout.txt'), 'rejected/compiler-output.txt', 'full compiler rejection; no proof or negative-control credit')
for name in ['preservation_check.py', 'preservation.json']:""")
replace("add(Path(__file__), 'assemble.py', 'exact assembly source')",
    "add(ROOT / 'prepare_assembly.py', 'prepare_assembly.py', 'exact assembly derivation source')\nadd(Path(__file__), 'assemble.py', 'exact assembly source')")
source = source.replace('SUCCESSFULLY_LOADED_SCT_CAPACITY_LOCAL_INSERT_CACHE_WRITE_AND_NOTE_EVENT_ORDER_QUALIFIED',
    'DERIVED_ALL_RETURN_NOTE_RESHAPE_AND_FEE_FUNDING_VERIFIABLE_NONVERIFIABLE_CACHE_FRAMES_QUALIFIED')
source = source.replace("'fresh_definition_audits': 5, 'fresh_theorem_audits': 8", "'fresh_definition_audits': 1, 'fresh_theorem_audits': 6")
source = source.replace("'fresh_complete_public_audits': 13", "'fresh_complete_public_audits': 7")
source = source.replace("'inherited_complete_public_audits': 97", "'inherited_complete_public_audits': 110")
source = source.replace("'rejected_attempts': 0", "'rejected_attempts': 1, 'rejected_proof_credit': 0")
start = source.index("'scope': mapping['scope'] + ")
end = source.index("\ndump(ROOT / 'review.json', review)", start)
source = source[:start] + """'scope': mapping['scope'] + ' Verifiable and nonverifiable cache writes are derived unchanged for all returned primitive and arbitrary-list note results, including errors, from their executable object/event-only writes. No opaque callback frame is a premise. The complete note reshape and FeeFunding raw action inherit this result; earlier objects/events may remain altered on an error and are not claimed rolled back. The supplied cache can include earlier body Volume writes, which FeeFunding preserves. Actual getter panics, Clone/COW, key/value/event codecs, tree and reader semantics, fee charging outside this raw action, block finalization and participating-store durability remain distinct interfaces. Original rejected elaboration is zero credit.'}
""".rstrip() + source[end:]
source = source.replace("'fresh_audits': 13", "'fresh_audits': 7").replace("'inherited_audits': 97", "'inherited_audits': 110")
(ROOT / 'assemble.py').write_text(source)
print({'fresh_reports': 7, 'inherited_reports': 110, 'owned_modules': 7, 'rejected_credit': 0})
