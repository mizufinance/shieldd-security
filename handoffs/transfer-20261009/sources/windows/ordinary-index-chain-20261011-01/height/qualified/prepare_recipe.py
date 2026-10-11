"""Prepare actual current-view height source on exact indexed-value closure."""
from pathlib import Path
import re
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
assert not (ROOT / 'prepare.py').exists()
source = (DIAG / 'transfer-ordinary-indexed-values-20261011-01/prepare.py').read_text()
def replace(before, after):
    global source
    assert source.count(before) == 1, before
    source = source.replace(before, after)
replace("UPSTREAM = DIAG / 'transfer-ordinary-index-delivery-20261011-02'", "UPSTREAM = DIAG / 'transfer-ordinary-indexed-values-20261011-01'")
source = source.replace('transfer-ordinary-indexed-values-owned-floor-20261011-01', 'transfer-ordinary-height-owned-floor-20261011-01')
source = source.replace("MODULE = 'TransferOrdinaryIndexedValues01'", "MODULE = 'TransferOrdinaryHeightSource01'")
source = source.replace('TransferOrdinaryIndexDelivery01', 'TransferOrdinaryIndexedValues01')
replace('assert len(current) == 6', 'assert len(current) == 2')
replace('assert len(records) == 17 and len(audits) == 227', 'assert len(records) == 18 and len(audits) == 229')
replace("'objects': 17", "'objects': 18")
source = source.replace('Complete seventeen-module first owned root; 227 inherited full reports.', 'Complete eighteen-module first owned root; 229 inherited full reports.')
source = source.replace('assert len(names) == 2', 'assert len(names) == 5')
start = source.index("prior_mapping = json.loads((UPSTREAM / 'source-mapping.json').read_bytes())")
end = source.index("\nmapping_file = ROOT / 'source-mapping.json'", start)
source = source[:start] + """prior_mapping = json.loads((UPSTREAM / 'source-mapping.json').read_bytes())
mapping = {'runtime_sha': prior_mapping['runtime_sha'],
    'runtime_sources': prior_mapping['runtime_sources'] + [pin(runtime / n) for n in [
        'crates/core/component/sct/src/component/clock.rs', 'crates/core/component/sct/src/state_key.rs']],
    'interfaces': prior_mapping['interfaces'] + ['Actual get_proto height decoder and height-key projection/store read availability remain representation interfaces; explicit separation from the two volume marker keys'],
    'scope': 'Height getter is installed as current verifiable overlay read plus decode, with unavailable, absent and decode-error outcomes refusing height success. Executable bound Ordinary body preserves every other V key on all returned results, without callback frame premises. Whole same-action per-transaction success derives original parent height bytes, actual decoder-to-height observation, successful read availability, index inspection at that height and unchanged final encoded height under explicit volume/height key separation. No desired body success, stable-height callback or original height value is assumed. All inherited token/extractor/proof/Rust/representation/tree/store/native/block/durability interfaces and full Transfer remain open.'}
""".rstrip() + source[end:]
source = source.replace('SAME_ACTION_ORDINARY_VISIBLE_INDEX_VALUES_AND_ORIGINAL_PARENT_NV_FRAME', 'CURRENT_VIEW_HEIGHT_GETTER_DERIVED_FROM_WHOLE_ORDINARY_INDEX_SUCCESS')
start = source.index("plan['source_repairs'] = ")
end = source.index("\nplan['artifact_policy']", start)
source = source[:start] + "plan['source_repairs'] = 'Fresh finite current-overlay height read/decode and Ordinary V-frame source; unchanged complete guards/audits and no ancestor replay.'" + source[end:]
source = source.replace('complete seventeen-module owned root', 'complete eighteen-module owned root')
source = source.replace('ORDINARY_INDEXED_VALUES_COMPLETE_SEVENTEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN', 'ORDINARY_HEIGHT_COMPLETE_EIGHTEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
source = source.replace("'fresh_audits': 2, 'inherited_audits': 227", "'fresh_audits': 5, 'inherited_audits': 229")
(ROOT / 'prepare.py').write_text(source)
handwritten = ROOT / 'handwritten/TransferOrdinaryHeightSource01.lean'
lean = handwritten.read_text()
names = re.findall(r'^(?:structure|inductive|def|theorem) ([A-Za-z0-9_]+)', lean, re.M)
assert len(names) == 5 and '#check' not in lean
audits = '\n'.join('set_option pp.all true in\n#check @' + n + '\n#print axioms ' + n for n in names)
lean = lean.replace('\nend ShielddSecurity.TransferOrdinaryHeightSource01', '\n' + audits + '\n\nend ShielddSecurity.TransferOrdinaryHeightSource01')
handwritten.write_text(lean)
print({'fresh_audits': len(names), 'inherited_audits': 229, 'owned_modules': 18})
