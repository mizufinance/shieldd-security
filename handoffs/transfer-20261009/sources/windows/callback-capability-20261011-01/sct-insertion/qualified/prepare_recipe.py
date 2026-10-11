"""Reuse exact complete-package guard for successful-load SCT insertion."""
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent / 'transfer-note-manager-source-20261011-03/prepare.py'
assert not (ROOT / 'prepare.py').exists() and not (ROOT / 'plan.json').exists()
source = BASE.read_text()
source = source.replace('TransferNoteManagerSource01', 'TransferSctInsertionSource01')
source = source.replace('transfer-note-manager-owned-floor-20261011-03', 'transfer-sct-insertion-owned-floor-20261011-01')
source = source.replace("UPSTREAM = DIAG / 'transfer-raw-effects-source-20261011-04'", "UPSTREAM = DIAG / 'transfer-note-manager-source-20261011-03'")
source = source.replace('TransferRawEffectsSource01', 'TransferNoteManagerSource01')
source = source.replace('len(current) == 27', 'len(current) == 13')
source = source.replace('len(records) == 5 and len(audits) == 84', 'len(records) == 6 and len(audits) == 97')
source = source.replace("'objects': 5", "'objects': 6").replace('Complete five-module first owned root; 84 inherited full reports.',
    'Complete six-module first owned root; 97 inherited full reports.')
source = source.replace("'inherited_audits': 84", "'inherited_audits': 97")
source = source.replace("ROOT / 'prepare_successor.py'", "ROOT / 'prepare_recipe.py'")
source = source.replace('note_manager_complete_auditor', 'sct_insertion_complete_auditor')
source = source.replace('NOTE_MANAGER_SOURCE_AND_COMPLETE_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN',
    'SCT_INSERTION_SOURCE_AND_COMPLETE_SIX_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
source = source.replace('NOTE_MANAGER_SCT_POSITION_PENDING_APPEND_AND_RAW_CALLBACK_COMPOSITION',
    'SUCCESSFULLY_LOADED_SCT_LOCAL_INSERT_CACHE_WRITE_AND_COMMITMENT_EVENT')
source = source.replace('complete five-module owned root', 'complete six-module owned root')
source = source.replace('Autonomous serial narrow NoteManager callback proof', 'Autonomous serial narrow successful-load SCT insertion proof')
source = source.replace('Fresh 03 replays byte-identical successful02 manager source with the qualified raw04 ancestor whose false-context declaration names are corrected to FeeFunding. No manager definitions, contracts, source bytes, guards or audits changed. Qualified02 and rejected01 remain preserved.',
    'Fresh successfully-loaded SCT source branch: capacity and local insert precede one SCT object write and one commitment event. No load panic is translated into Err. Exact qualified manager closure and all guards unchanged.')
start = source.index('mapping = ')
end = source.index("mapping_file = ROOT / 'source-mapping.json'", start)
source = source[:start] + '''mapping = {'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'runtime_sources': [pin(runtime / n) for n in ['crates/core/component/sct/src/component/tree.rs',
        'crates/core/component/sct/src/state_key.rs', 'crates/core/component/shielded-pool/src/component/note_manager.rs',
        'crates/core/component/shielded-pool/src/component/action_handler/note_reshape.rs']],
    'interfaces': ['Model starts after get_sct successfully returns a tree; expect panic for loader failure is outside returned-result scope, not a recoverable modeled error',
        'loaded denotes that successful immutable tree snapshot; actual NV loading/authentication and cached getter correspondence remain explicit',
        'position returns full position and commitment component; real u16 commitment bound used<65536 and tree position meaning remain representation interfaces',
        'Pure localInsert callback represents Witness::Forget insertion into the locally cloned tree; real tree insertion/position/root semantics and Clone/COW isolation remain explicit',
        'Tree encoding/cache key, commitment/source/event codec and object cache projection remain explicit',
        'Exact pending-manager and inherited raw/storage/reader/ownership/durability interfaces remain open'],
    'scope': 'Functional add_sct_commitment source branch after successful tree loading: capacity check then local insert, followed only on success by one SCT cache object write and one commitment event. Returned capacity/insert errors derive input-cache retention in the immutable local model. NoteManager installation derives semantic-event suppression on missing position and commitment-before-note-created event order on success. Actual getter panic, Clone/COW, tree semantics, native execution, durable/Merkle correspondence, atomic evidence refresh and full Transfer remain open.'}
''' + source[end:]
source = source.replace('Prepare exact SCT/pending callback facts on the complete qualified closure.',
    'Prepare the successfully-loaded SCT insertion branch on the complete qualified closure.')
(ROOT / 'prepare.py').write_text(source)
print({'fresh_reports': 13, 'inherited_reports': 97, 'owned_modules': 6, 'guard_delta': 'NONE', 'native_credit': 0})
