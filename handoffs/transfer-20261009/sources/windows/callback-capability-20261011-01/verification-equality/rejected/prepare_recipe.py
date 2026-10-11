"""Reuse strict complete-package admission for native compared-field identity."""
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent / 'transfer-note-manager-source-20261011-03/prepare.py'
assert not (ROOT / 'prepare.py').exists() and not (ROOT / 'plan.json').exists()
source = BASE.read_text()
source = source.replace('TransferNoteManagerSource01', 'TransferVerificationEqualitySource01')
source = source.replace('transfer-note-manager-owned-floor-20261011-03', 'transfer-verification-equality-owned-floor-20261011-01')
source = source.replace("UPSTREAM = DIAG / 'transfer-raw-effects-source-20261011-04'", "UPSTREAM = DIAG / 'transfer-capability-source-20261011-02'")
source = source.replace('TransferRawEffectsSource01', 'TransferCapabilitySource01')
source = source.replace('len(current) == 27', 'len(current) == 11')
source = source.replace('len(records) == 5 and len(audits) == 84', 'len(records) == 6 and len(audits) == 95')
source = source.replace("'objects': 5", "'objects': 6").replace('Complete five-module first owned root; 84 inherited full reports.',
    'Complete six-module first owned root; 95 inherited full reports.')
source = source.replace("'inherited_audits': 84", "'inherited_audits': 95")
source = source.replace("ROOT / 'prepare_successor.py'", "ROOT / 'prepare_recipe.py'")
source = source.replace('note_manager_complete_auditor', 'verification_equality_complete_auditor')
source = source.replace("assert len(names) == 13 and re.findall", "names += ['instDecidableEqItem']\nassert len(names) == 13 and re.findall")
source = source.replace('NOTE_MANAGER_SOURCE_AND_COMPLETE_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN',
    'VERIFICATION_EQUALITY_SOURCE_AND_COMPLETE_SIX_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
source = source.replace('NOTE_MANAGER_SCT_POSITION_PENDING_APPEND_AND_RAW_CALLBACK_COMPOSITION',
    'VERIFICATION_FIELDWISE_EQUALITY_AND_VERIFIED_FAMILY_ITEM_BINDING')
source = source.replace('complete five-module owned root', 'complete six-module owned root')
source = source.replace('Autonomous serial narrow NoteManager callback proof', 'Autonomous serial narrow verification equality proof')
source = source.replace('Fresh 03 replays byte-identical successful02 manager source with the qualified raw04 ancestor whose false-context declaration names are corrected to FeeFunding. No manager definitions, contracts, source bytes, guards or audits changed. Qualified02 and rejected01 remain preserved.',
    'Fresh explicit family/statement-scalar/serialized-envelope comparison and ensure_binds source model. Complete derived DecidableEq instance is included in the full type/axiom census. All ancestors and guards unchanged; statement-preimage semantics and registry verification remain separate.')
start = source.index('mapping = ')
end = source.index("mapping_file = ROOT / 'source-mapping.json'", start)
source = source[:start] + '''mapping = {'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'runtime_sources': [pin(runtime / n) for n in ['crates/crypto/proof-params/src/pari.rs',
        'crates/core/component/shielded-pool/src/component/action_handler/transfer.rs']],
    'interfaces': ['Family/scalar/envelope-byte indices represent the actual compared fields; scalar field and envelope.to_bytes representation correspondence remain explicit',
        'Equality of the statement scalar is identity of that compared scalar, not equality of source statement preimages or semantic correspondence',
        'Generic complete-item capability model is instantiated by the compared-field tuple; action extraction and Item-to-effect projection remain upstream interfaces',
        'Verified token must be minted by the correct registry and exact Transfer proof verification; ensure_binds itself does not check registry_id',
        'All inherited raw/SCT/reader/ownership/durability interfaces and native/full Transfer gates remain open'],
    'scope': 'Functional Verification::eq and Verified::ensure_binds compare the actual family, statement scalar and serialized envelope bytes. Success derives every compared field and requested family. Registry identifier independence is explicit. Mismatched fields refuse symbolically; no runtime negative-control credit. Exact fieldwise item matching dispatches the qualified capability wrapper. Crypto verification, statement-preimage/semantic correspondence, actual scalar/serializer codecs, native execution, atomic evidence refresh and full Transfer remain open.'}
''' + source[end:]
source = source.replace('Prepare exact SCT/pending callback facts on the complete qualified closure.',
    'Prepare actual Verification compared-field equality on the complete qualified closure.')
(ROOT / 'prepare.py').write_text(source)
print({'fresh_reports': 13, 'inherited_reports': 95, 'owned_modules': 6, 'guard_delta': 'NONE', 'native_credit': 0})
