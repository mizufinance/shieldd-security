"""Fresh complete current-volume closure; derive all-return Ordinary storage proof."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
assert not (ROOT / 'prepare.py').exists()
source = (DIAG / 'transfer-current-volume-source-20261011-02/prepare.py').read_text()
def replace(before, after):
    global source
    assert source.count(before) == 1, before
    source = source.replace(before, after)

replace("UPSTREAM = DIAG / 'transfer-raw-source-frames-20261011-02'", "UPSTREAM = DIAG / 'transfer-current-volume-source-20261011-02'")
source = source.replace('transfer-current-volume-owned-floor-20261011-02', 'transfer-ordinary-storage-owned-floor-20261011-01')
source = source.replace("MODULE = 'TransferCurrentVolumeSource01'", "MODULE = 'TransferOrdinaryStorageSource01'")
source = source.replace('TransferRawSourceFrames01', 'TransferCurrentVolumeSource01')
replace('assert len(current) == 7', 'assert len(current) == 9')
replace('assert len(records) == 8 and len(audits) == 117', 'assert len(records) == 9 and len(audits) == 126')
replace("'objects': 8", "'objects': 9")
source = source.replace('Complete eight-module first owned root; 117 inherited full reports.', 'Complete nine-module first owned root; 126 inherited full reports.')
source = source.replace('assert len(names) == 9', 'assert len(names) == 12')
source = source.replace("ROOT / 'prepare_successor.py'", "ROOT / 'prepare_recipe.py'")
start = source.index("mapping = {'runtime_sha':")
end = source.index("\nmapping_file = ROOT / 'source-mapping.json'", start)
source = source[:start] + """mapping = {'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'runtime_sources': [pin(runtime / n) for n in ['crates/core/component/shielded-pool/src/component/shielded_pool.rs',
        'crates/core/component/shielded-pool/src/component/action_handler/transfer.rs',
        'crates/core/component/shielded-pool/src/component/note_manager.rs',
        'crates/core/component/shielded-pool/src/component/action_handler/note_reshape.rs',
        'crates/core/component/sct/src/component/tree.rs']],
    'interfaces': ['Successfully loaded immutable SCT source branch; actual get_sct expect panic and Clone/COW remain distinct',
        'Local tree insert, position extraction and commitment/payload/source/event encodings remain explicit modeled interfaces',
        'Current volume get_raw availability and day/nullifier key projections require Rust/store correspondence',
        'Nullifier pending getter and authenticated durable reader semantics remain inherited interfaces',
        'Same exact action, proof context, token, public-item equality and cryptographic proof provenance remain upstream',
        'Raw action cache framing does not imply block finalization, fee charging or participating-store durability',
        'No native or compiler-error negative-control credit and no full Transfer certificate'],
    'scope': 'Both note and volume callbacks are executable SCT insertion and post-SCT pending-object append, without opaque callback frame premises. Arbitrary Ordinary execution returned results preserve input nonverifiable writes and either preserve verifiable writes or add exactly the two volume marker writes. Whole execution success derives exact capability match, initially absent current overlay entry, and both marker writes, without successful reshape or desired read/poststate premises. Earlier objects/events may remain altered on errors. Rust/tree/store/ownership/proof and full Transfer interfaces remain open.'}
""".rstrip() + source[end:]
source = source.replace("plan['kind'] = 'CURRENT_CHILD_OVERLAY_VOLUME_EXISTENCE_DERIVES_ORDINARY_AND_DELIVERY_REFUSAL'", "plan['kind'] = 'BOTH_SCT_CALLBACKS_DERIVE_ORDINARY_STORAGE_FRAMING_AND_SUCCESS_MARKERS'")
start = source.index("plan['source_repairs'] = ")
end = source.index("\nplan['artifact_policy']", start)
source = source[:start] + "plan['source_repairs'] = 'Fresh first source; symbolic all-return framing and whole success inversion with finite reusable lemmas; no guard or audit relaxation.'" + source[end:]
source = source.replace('complete eight-module owned root', 'complete nine-module owned root')
source = source.replace('CURRENT_VOLUME_SOURCE_AND_COMPLETE_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN', 'ORDINARY_STORAGE_AND_COMPLETE_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
source = source.replace("'fresh_audits': 9, 'inherited_audits': 117", "'fresh_audits': 12, 'inherited_audits': 126")
(ROOT / 'prepare.py').write_text(source)
handwritten = ROOT / 'handwritten/TransferOrdinaryStorageSource01.lean'
lean = handwritten.read_text()
names = re.findall(r'^(?:structure|inductive|def|theorem) ([A-Za-z0-9_]+)', lean, re.M)
assert len(names) == 12
assert '#check' not in lean
audits = '\n'.join('set_option pp.all true in\n#check @' + n + '\n#print axioms ' + n for n in names)
lean = lean.replace('\nend ShielddSecurity.TransferOrdinaryStorageSource01', '\n' + audits + '\n\nend ShielddSecurity.TransferOrdinaryStorageSource01')
handwritten.write_text(lean)
print({'fresh_audits': len(names), 'inherited_audits': 126, 'owned_modules': 9})
