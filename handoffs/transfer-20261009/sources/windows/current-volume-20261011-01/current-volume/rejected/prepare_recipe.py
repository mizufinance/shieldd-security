"""Reuse strict source admission for overlay-derived ordinary volume refusal."""
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent / 'transfer-note-manager-source-20261011-03/prepare.py'
assert not (ROOT / 'prepare.py').exists() and not (ROOT / 'plan.json').exists()
source = BASE.read_text()
source = source.replace('TransferNoteManagerSource01', 'TransferCurrentVolumeSource01')
source = source.replace('transfer-note-manager-owned-floor-20261011-03', 'transfer-current-volume-owned-floor-20261011-01')
source = source.replace("UPSTREAM = DIAG / 'transfer-raw-effects-source-20261011-04'", "UPSTREAM = DIAG / 'transfer-raw-source-frames-20261011-02'")
source = source.replace('TransferRawEffectsSource01', 'TransferRawSourceFrames01')
source = source.replace('len(current) == 27', 'len(current) == 7')
source = source.replace('len(records) == 5 and len(audits) == 84', 'len(records) == 8 and len(audits) == 117')
source = source.replace("'objects': 5", "'objects': 8").replace('Complete five-module first owned root; 84 inherited full reports.',
    'Complete eight-module first owned root; 117 inherited full reports.')
source = source.replace("'inherited_audits': 84", "'inherited_audits': 117")
source = source.replace('len(names) == 13', 'len(names) == 8').replace("'fresh_audits': 13", "'fresh_audits': 8")
source = source.replace("ROOT / 'prepare_successor.py'", "ROOT / 'prepare_recipe.py'")
source = source.replace('note_manager_complete_auditor', 'current_volume_complete_auditor')
source = source.replace('NOTE_MANAGER_SOURCE_AND_COMPLETE_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN',
    'CURRENT_VOLUME_SOURCE_AND_COMPLETE_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
source = source.replace('NOTE_MANAGER_SCT_POSITION_PENDING_APPEND_AND_RAW_CALLBACK_COMPOSITION',
    'CURRENT_CHILD_OVERLAY_VOLUME_EXISTENCE_DERIVES_ORDINARY_AND_DELIVERY_REFUSAL')
source = source.replace('complete five-module owned root', 'complete eight-module owned root')
source = source.replace('Autonomous serial narrow NoteManager callback proof', 'Autonomous serial narrow current-volume overlay source proof')
source = source.replace('Fresh 03 replays byte-identical successful02 manager source with the qualified raw04 ancestor whose false-context declaration names are corrected to FeeFunding. No manager definitions, contracts, source bytes, guards or audits changed. Qualified02 and rejected01 remain preserved.',
    'Fresh current volume read from child-overlay verifiable presence, with distinct read availability. Existing volume precludes any Ordinary raw success and enclosing delivery/parent-queue mutation without successful reshape or desired spent flag premises. All inherited guards and evidence unchanged.')
start = source.index('mapping = ')
end = source.index("mapping_file = ROOT / 'source-mapping.json'", start)
source = source[:start] + '''mapping = {'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'runtime_sources': [pin(runtime / n) for n in ['crates/core/component/shielded-pool/src/component/shielded_pool.rs',
        'crates/core/component/shielded-pool/src/component/action_handler/transfer.rs',
        'crates/core/component/shielded-pool/src/state_key.rs', 'third_party/cnidarium-0.83.0/src/delta.rs',
        'third_party/cnidarium-0.83.0/src/cache.rs']],
    'interfaces': ['Actual volume get_raw and day/nullifier key projection correspond to current functional parent/child verifiable overlay; read availability/error remains an explicit store interface',
        'Any present byte value is spent, matching is_some; no marker-value correctness premise or absent-versus-read-error conflation',
        'Installed note/SCT model uses successfully loaded immutable trees; actual getter panic, Clone/COW, local tree semantics, pending codecs and reader interfaces remain inherited',
        'Same decoded action/context/verified-token and public-item semantic projection provenance remain upstream',
        'Returned-result raw/delivery refusal is scoped to the functional source program; native Host panic/retry and participating-store durability remain separate',
        'No hash injectivity, compiler-error negative-control credit, atomic evidence refresh or full Transfer certificate follows'],
    'scope': 'Functional current-overlay volume existence check and source-derived Ordinary refusal. Existing child-overlay value cannot disappear through modeled note reshape V/NV framing. Whole Ordinary raw execution returns no successful cache regardless of reshape outcome, source availability or read availability; enclosing delivery rejects an existing parent entry and preserves original parent/queue. No successful reshape, desired current spent flag or desired rollback premise. Native Rust/store/key/clone/tree correspondence and full Transfer remain open.'}
''' + source[end:]
source = source.replace('Prepare exact SCT/pending callback facts on the complete qualified closure.',
    'Prepare overlay-derived current volume refusal on the complete qualified closure.')
(ROOT / 'prepare.py').write_text(source)
print({'fresh_reports': 8, 'inherited_reports': 117, 'owned_modules': 8, 'guard_delta': 'NONE', 'native_credit': 0})
