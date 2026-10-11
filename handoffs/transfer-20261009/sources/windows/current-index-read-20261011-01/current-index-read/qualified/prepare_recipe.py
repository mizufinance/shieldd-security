"""Prepare current-overlay index reads and original-parent duplicate refusal."""
from pathlib import Path
import re
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
assert not (ROOT / 'prepare.py').exists()
source = (DIAG / 'transfer-ordinary-height-source-20261011-01/prepare.py').read_text()
def replace(before, after):
    global source
    assert source.count(before) == 1, before
    source = source.replace(before, after)
replace("UPSTREAM = DIAG / 'transfer-ordinary-indexed-values-20261011-01'", "UPSTREAM = DIAG / 'transfer-volume-height-keys-20261011-01'")
source = source.replace('transfer-ordinary-height-owned-floor-20261011-01', 'transfer-ordinary-index-read-owned-floor-20261011-01')
source = source.replace("MODULE = 'TransferOrdinaryHeightSource01'", "MODULE = 'TransferOrdinaryIndexReadSource01'")
source = source.replace('TransferOrdinaryIndexedValues01', 'TransferVolumeHeightKeys01')
replace('assert len(current) == 2', 'assert len(current) == 9')
replace('assert len(records) == 18 and len(audits) == 229', 'assert len(records) == 20 and len(audits) == 243')
replace("'objects': 18", "'objects': 20")
source = source.replace('Complete eighteen-module first owned root; 229 inherited full reports.', 'Complete twenty-module first owned root; 243 inherited full reports.')
replace("'handwritten/TransferVolumeHeightKeys01.lean'", "'portable-source/TransferVolumeHeightKeys01.lean'")
source = source.replace('assert len(names) == 5', 'assert len(names) == 7')
start = source.index("prior_mapping = json.loads((UPSTREAM / 'source-mapping.json').read_bytes())")
end = source.index("\nmapping_file = ROOT / 'source-mapping.json'", start)
source = source[:start] + """prior_mapping = json.loads((UPSTREAM / 'source-mapping.json').read_bytes())
mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': prior_mapping['runtime_sources'],
    'interfaces': prior_mapping['interfaces'] + ['Actual nonverifiable_get_raw availability, transaction conversion/serialization and initial stored-height decoder correspondence remain explicit'],
    'scope': 'Concrete current-overlay index reads distinguish unavailable from absent data, with every present byte value treated as an existing identifier. Available existing-ID read derives exact semantic duplicate error; unavailable read refuses success without being counted as a duplicate control. Whole same-action Ordinary delivery with source-separated volume/height keys, decoded original parent height and existing parent ID entry is rejected for every extractor/body outcome and read availability. Executable body NV frame preserves that ID until inspection, and current height read preserves the original decoded height; parent and queue remain original after enclosing refusal. No successful body, desired index error, stable-height callback or rollback poststate is assumed. Initial state/conversion/decoder inputs and inherited proof/token/Rust/key/store/tree/native/block/durability remain interfaces. Full Transfer open; no native or semantic negative-control credit.'}
""".rstrip() + source[end:]
source = source.replace('CURRENT_VIEW_HEIGHT_GETTER_DERIVED_FROM_WHOLE_ORDINARY_INDEX_SUCCESS', 'CURRENT_OVERLAY_INDEX_READS_DERIVE_WHOLE_ORDINARY_DUPLICATE_ID_REFUSAL')
start = source.index("plan['source_repairs'] = ")
end = source.index("\nplan['artifact_policy']", start)
source = source[:start] + "plan['source_repairs'] = 'Fresh finite source installs NV read primitives and proves existing-parent duplicate refusal through the qualified whole Ordinary source. All guards/audits unchanged; no ancestors replayed.'" + source[end:]
source = source.replace('complete eighteen-module owned root', 'complete twenty-module owned root')
source = source.replace('ORDINARY_HEIGHT_COMPLETE_EIGHTEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN', 'ORDINARY_INDEX_READ_COMPLETE_TWENTY_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
source = source.replace("'fresh_audits': 5, 'inherited_audits': 229", "'fresh_audits': 7, 'inherited_audits': 243")
(ROOT / 'prepare.py').write_text(source)
handwritten = ROOT / 'handwritten/TransferOrdinaryIndexReadSource01.lean'
lean = handwritten.read_text()
names = re.findall(r'^(?:structure|inductive|def|theorem) ([A-Za-z0-9_]+)', lean, re.M)
assert len(names) == 7 and '#check' not in lean
audits = '\n'.join('set_option pp.all true in\n#check @' + n + '\n#print axioms ' + n for n in names)
lean = lean.replace('\nend ShielddSecurity.TransferOrdinaryIndexReadSource01', '\n' + audits + '\n\nend ShielddSecurity.TransferOrdinaryIndexReadSource01')
handwritten.write_text(lean)
print({'fresh_audits': len(names), 'inherited_audits': 243, 'owned_modules': 20})
