"""Prepare the same-action visible-value and original-parent NV frame join."""
from pathlib import Path
import re
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
assert not (ROOT / 'prepare.py').exists()
source = (DIAG / 'transfer-ordinary-index-delivery-20261011-02/prepare.py').read_text()
def replace(before, after):
    global source
    assert source.count(before) == 1, before
    source = source.replace(before, after)
replace("UPSTREAM = DIAG / 'transfer-bound-ordinary-source-20261011-02'", "UPSTREAM = DIAG / 'transfer-ordinary-index-delivery-20261011-02'")
source = source.replace('transfer-ordinary-index-delivery-owned-floor-20261011-02', 'transfer-ordinary-indexed-values-owned-floor-20261011-01')
source = source.replace("MODULE = 'TransferOrdinaryIndexDelivery01'", "MODULE = 'TransferOrdinaryIndexedValues01'")
source = source.replace('TransferBoundOrdinarySource01', 'TransferOrdinaryIndexDelivery01')
replace('assert len(current) == 12', 'assert len(current) == 6')
replace('assert len(records) == 13 and len(audits) == 174', 'assert len(records) == 17 and len(audits) == 227')
start = source.index("inspection = DIAG / 'transfer-index-inspection-20261011-02'")
end = source.index('POOL.mkdir()', start)
source = source[:start] + source[end:]
replace("'objects': 16", "'objects': 17")
source = source.replace('Complete sixteen-module first owned root; 221 inherited full reports; shared cache/raw source objects and 28 full reports counted once.', 'Complete seventeen-module first owned root; 227 inherited full reports. Exact qualified source/object closure and complete reports reused without replay.')
source = source.replace('assert len(names) == 6', 'assert len(names) == 2')
source = source.replace("ROOT / 'prepare_successor.py'", "ROOT / 'prepare_recipe.py'")
replace("'imports': ['ShielddSecurity.TransferOrdinaryIndexDelivery01', 'ShielddSecurity.TransferIndexInspectionFacts01']", "'imports': ['ShielddSecurity.TransferOrdinaryIndexDelivery01']")
start = source.index('runtime_rows = ')
end = source.index("\nmapping_file = ROOT / 'source-mapping.json'", start)
source = source[:start] + """prior_mapping = json.loads((UPSTREAM / 'source-mapping.json').read_bytes())
mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': prior_mapping['runtime_sources'],
    'interfaces': prior_mapping['interfaces'] + ['Index byte-to-Nat projection injectivity denotes key representation preservation and is not a cryptographic hash injectivity claim'],
    'scope': 'The identical action argument drives stateless Ordinary Item extraction, raw input/output projections, transaction conversion and per-transaction indexing. Whole delivery success derives exact re-extraction, initially absent parent volume entry, both visible V markers, exact NV entry payload/ID ordinal/next count values and unchanged queue. Index byte suffix separation derives projected key separation under explicit representation injectivity. Every NV key outside those three actual index keys retains its original parent value, derived from executable body NV framing and index writes rather than an opaque callback premise. No desired body/index success or target cache is assumed. All inherited proof/token/extractor/Rust/representation/store/native/block/durability and full Transfer interfaces remain open.'}
""".rstrip() + source[end:]
source = source.replace('ORDINARY_BODY_AND_CONCRETE_TRANSACTION_INDEX_WHOLE_DELIVERY_SUCCESS', 'SAME_ACTION_ORDINARY_VISIBLE_INDEX_VALUES_AND_ORIGINAL_PARENT_NV_FRAME')
start = source.index("plan['source_repairs'] = ")
end = source.index("\nplan['artifact_policy']", start)
source = source[:start] + "plan['source_repairs'] = 'Fresh two-theorem finite join, sharing the same action argument across every modeled stage. No ancestors replayed and all guards, audits and semantic interfaces unchanged.'" + source[end:]
source = source.replace('complete sixteen-module owned root', 'complete seventeen-module owned root')
source = source.replace('ORDINARY_INDEX_DELIVERY_COMPLETE_SIXTEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN', 'ORDINARY_INDEXED_VALUES_COMPLETE_SEVENTEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
source = source.replace("'fresh_audits': 6, 'inherited_audits': 221", "'fresh_audits': 2, 'inherited_audits': 227")
(ROOT / 'prepare.py').write_text(source)
handwritten = ROOT / 'handwritten/TransferOrdinaryIndexedValues01.lean'
lean = handwritten.read_text()
names = re.findall(r'^(?:structure|inductive|def|theorem) ([A-Za-z0-9_]+)', lean, re.M)
assert len(names) == 2 and '#check' not in lean
audits = '\n'.join('set_option pp.all true in\n#check @' + n + '\n#print axioms ' + n for n in names)
lean = lean.replace('\nend ShielddSecurity.TransferOrdinaryIndexedValues01', '\n' + audits + '\n\nend ShielddSecurity.TransferOrdinaryIndexedValues01')
handwritten.write_text(lean)
print({'fresh_audits': len(names), 'inherited_audits': 227, 'owned_modules': 17})
