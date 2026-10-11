"""Reuse strict serial admission for derived raw storage-domain frames."""
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent / 'transfer-note-manager-source-20261011-03/prepare.py'
assert not (ROOT / 'prepare.py').exists() and not (ROOT / 'plan.json').exists()
source = BASE.read_text()
source = source.replace('TransferNoteManagerSource01', 'TransferRawSourceFrames01')
source = source.replace('transfer-note-manager-owned-floor-20261011-03', 'transfer-raw-source-frames-owned-floor-20261011-01')
source = source.replace("UPSTREAM = DIAG / 'transfer-raw-effects-source-20261011-04'", "UPSTREAM = DIAG / 'transfer-sct-insertion-source-20261011-01'")
source = source.replace('TransferRawEffectsSource01', 'TransferSctInsertionSource01')
source = source.replace('len(current) == 27', 'len(current) == 13')
source = source.replace('len(records) == 5 and len(audits) == 84', 'len(records) == 7 and len(audits) == 110')
source = source.replace("'objects': 5", "'objects': 7").replace('Complete five-module first owned root; 84 inherited full reports.',
    'Complete seven-module first owned root; 110 inherited full reports.')
source = source.replace("'inherited_audits': 84", "'inherited_audits': 110")
source = source.replace('len(names) == 13', 'len(names) == 7').replace("'fresh_audits': 13", "'fresh_audits': 7")
source = source.replace("ROOT / 'prepare_successor.py'", "ROOT / 'prepare_recipe.py'")
source = source.replace('note_manager_complete_auditor', 'raw_frames_complete_auditor')
source = source.replace('NOTE_MANAGER_SOURCE_AND_COMPLETE_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN',
    'RAW_SOURCE_FRAMES_AND_COMPLETE_SEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
source = source.replace('NOTE_MANAGER_SCT_POSITION_PENDING_APPEND_AND_RAW_CALLBACK_COMPOSITION',
    'DERIVED_ALL_RETURN_NOTE_RESHAPE_AND_FEE_FUNDING_STORAGE_DOMAIN_FRAMES')
source = source.replace('complete five-module owned root', 'complete seven-module owned root')
source = source.replace('Autonomous serial narrow NoteManager callback proof', 'Autonomous serial narrow derived raw storage-domain frames proof')
source = source.replace('Fresh 03 replays byte-identical successful02 manager source with the qualified raw04 ancestor whose false-context declaration names are corrected to FeeFunding. No manager definitions, contracts, source bytes, guards or audits changed. Qualified02 and rejected01 remain preserved.',
    'Fresh symbolic recurrence derives V/NV cache frames from actual modeled nullifier/SCT/pending-object primitives, across all returned results. No desired callback-frame premise. Successful getter/immutable clone representation remains scoped; all guards and ancestors unchanged.')
start = source.index('mapping = ')
end = source.index("mapping_file = ROOT / 'source-mapping.json'", start)
source = source[:start] + '''mapping = {'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'runtime_sources': [pin(runtime / n) for n in ['crates/core/component/sct/src/component/tree.rs',
        'crates/core/component/shielded-pool/src/component/note_manager.rs',
        'crates/core/component/shielded-pool/src/component/action_handler/note_reshape.rs',
        'crates/core/component/shielded-pool/src/component/action_handler/transfer.rs',
        'crates/core/component/shielded-pool/src/volume_accumulator.rs']],
    'interfaces': ['The installed SCT backend models a successfully loaded immutable local tree; actual getter panic and Clone/COW isolation remain inherited interfaces',
        'Current pending getter and tree/object encodings, key projection, local insertion/position semantics and event codecs remain explicit',
        'Qualified nullifier reader/status/equality/capacity interfaces remain inherited',
        'Results concern the raw action child cache before index writing, SCT/block persistence and participating-store durability',
        'False ordinary flag is FeeFunding; fee charging outside this raw action and other actions/block finalization are not framed',
        'No Rust/store/Merkle semantic refinement, runtime negative-control credit, hash injectivity or full Transfer certificate follows'],
    'scope': 'Unbounded functional source composition derives V/NV cache preservation for SCT insertion, pending payload update, arbitrary note-output recurrence, public nullifier batch, complete note reshape and FeeFunding raw action, across all returned errors and success. No opaque callback-domain-frame premise is supplied. This relies on the explicitly scoped successfully loaded immutable SCT model and other named representation interfaces; native/durable/full Transfer closure remains open.'}
''' + source[end:]
source = source.replace('Prepare exact SCT/pending callback facts on the complete qualified closure.',
    'Prepare derived raw storage-domain frames on the complete qualified closure.')
(ROOT / 'prepare.py').write_text(source)
print({'fresh_reports': 7, 'inherited_reports': 110, 'owned_modules': 7, 'guard_delta': 'NONE', 'native_credit': 0})
