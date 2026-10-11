"""Reuse unchanged serial guard/pool machinery for exact capability binding."""
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent / 'transfer-note-manager-source-20261011-03/prepare.py'
assert not (ROOT / 'prepare.py').exists() and not (ROOT / 'plan.json').exists()
source = BASE.read_text()
source = source.replace('TransferNoteManagerSource01', 'TransferCapabilitySource01')
source = source.replace('transfer-note-manager-owned-floor-20261011-03', 'transfer-capability-owned-floor-20261011-01')
source = source.replace('len(names) == 13', 'len(names) == 11').replace("'fresh_audits': 13", "'fresh_audits': 11")
source = source.replace("ROOT / 'prepare_successor.py'", "ROOT / 'prepare_recipe.py'")
source = source.replace('note_manager_complete_auditor', 'capability_complete_auditor')
source = source.replace('NOTE_MANAGER_SOURCE_AND_COMPLETE_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN',
    'CAPABILITY_SOURCE_AND_COMPLETE_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
source = source.replace('NOTE_MANAGER_SCT_POSITION_PENDING_APPEND_AND_RAW_CALLBACK_COMPOSITION',
    'STATELESS_COMPLETE_ITEM_REEXTRACTION_AND_EXACT_VALIDATED_CAPABILITY_REBINDING')
source = source.replace('Autonomous serial narrow NoteManager callback proof', 'Autonomous serial narrow exact capability source proof')
source = source.replace('Fresh 03 replays byte-identical successful02 manager source with the qualified raw04 ancestor whose false-context declaration names are corrected to FeeFunding. No manager definitions, contracts, source bytes, guards or audits changed. Qualified02 and rejected01 remain preserved.',
    'Fresh exact capability source on the corrected Ordinary/FeeFunding raw04 closure. Existing source/evidence remains immutable; no extraction success, proof validity or desired exactMatched boolean is assumed by successful binding inversion.')
start = source.index('mapping = ')
end = source.index("mapping_file = ROOT / 'source-mapping.json'", start)
source = source[:start] + '''mapping = {'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'runtime_sources': [pin(runtime / n) for n in ['crates/core/component/shielded-pool/src/component/action_handler/transfer.rs',
        'crates/core/component/shielded-pool/src/component/action_handler/note_reshape.rs',
        'crates/core/component/shielded-pool/src/volume_accumulator.rs']],
    'interfaces': ['Generic Item is the complete decoded Verification value; actual Rust equality/encoding and full public field/proof correspondence remain explicit',
        'Pure extractor models anchor, shape, expected context, authorization, lengths, public extraction and proof item construction; its internal semantics remain upstream',
        'Validated token provenance requires exact Transfer family/item verified capability, compliance anchors, timestamp freshness and validation-time ordinary volume check; this wrapper does not establish those upstream checks',
        'Action inputs/output projection is the same captured action passed to extraction; decoded payload/effect projection correspondence remains explicit',
        'True ordinary flag is Ordinary; false is FeeFunding, exactly the runtime enum',
        'All inherited raw source/storage/SCT/reader/ownership/durability interfaces remain open'],
    'scope': 'Functional exact post-validation capability rebinding at raw execution. Whole execution success derives successful re-extraction of the token item through actual comparison, before dispatching projected action effects in the token context. Extraction/mismatch preserve input cache. Bound Ordinary late-volume conflict retains earlier raw cache; cryptography, extractor internals, native controls, atomic evidence refresh and full Transfer remain open.'}
''' + source[end:]
source = source.replace('Prepare exact SCT/pending callback facts on the complete qualified closure.',
    'Prepare exact capability rebinding facts on the complete qualified closure.')
(ROOT / 'prepare.py').write_text(source)
print({'base_guard_recipe_sha256': hashlib.sha256(BASE.read_bytes()).hexdigest(), 'fresh_reports': 11,
    'inherited_reports': 84, 'guard_delta': 'NONE', 'native_credit': 0})
