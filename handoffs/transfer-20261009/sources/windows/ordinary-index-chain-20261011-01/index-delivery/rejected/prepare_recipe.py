"""Admit narrow per-transaction source join over exact bound-body/index closure."""
from pathlib import Path
import re
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
assert not (ROOT / 'prepare.py').exists()
source = (DIAG / 'transfer-bound-ordinary-source-20261011-02/prepare.py').read_text()
def replace(before, after):
    global source
    assert source.count(before) == 1, before
    source = source.replace(before, after)
replace("UPSTREAM = DIAG / 'transfer-ordinary-storage-source-20261011-02'", "UPSTREAM = DIAG / 'transfer-bound-ordinary-source-20261011-02'")
source = source.replace('transfer-bound-ordinary-owned-floor-20261011-02', 'transfer-ordinary-index-delivery-owned-floor-20261011-01')
source = source.replace("MODULE = 'TransferBoundOrdinarySource01'", "MODULE = 'TransferOrdinaryIndexDelivery01'")
source = source.replace('TransferOrdinaryStorageSource01', 'TransferBoundOrdinarySource01')
source = source.replace('TransferVerificationEqualitySource01', 'TransferIndexInspectionFacts01')
source = source.replace('transfer-verification-equality-source-20261011-02', 'transfer-index-inspection-20261011-02')
source = source.replace('eq_', 'inspection_').replace('equality', 'inspection')
replace('assert len(records) == 10 and len(audits) == 138', 'assert len(records) == 13 and len(audits) == 174')
replace('assert len(inspection_reports) == 13', 'assert len(inspection_reports) == 16')
replace('assert len(records) == 12 and len(audits) == 162', 'assert len(records) == 16 and len(audits) == 221')
replace("'objects': 12", "'objects': 16")
source = source.replace('Complete twelve-module first owned root; 162 inherited full reports; shared five-module raw ancestry verified once.', 'Complete sixteen-module first owned root; 221 inherited full reports; shared cache/raw source objects and 28 full reports counted once.')
source = source.replace('assert len(names) == 12', 'assert len(names) == 6')
source = source.replace("ROOT / 'prepare_successor.py'", "ROOT / 'prepare_recipe.py'")
start = source.index("mapping = {'runtime_sha':")
end = source.index("\nmapping_file = ROOT / 'source-mapping.json'", start)
source = source[:start] + """runtime_rows = json.loads((UPSTREAM / 'source-mapping.json').read_bytes())['runtime_sources'] + json.loads((inspection / 'source-mapping.json').read_bytes())['runtime_sources']
runtime_union = {}
for row in runtime_rows:
    assert pin(row['path']) == row
    assert row['path'] not in runtime_union or runtime_union[row['path']] == row
    runtime_union[row['path']] = row
mapping = {'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'runtime_sources': list(runtime_union.values()),
    'interfaces': ['Generic body adapter is instantiated with the qualified exact-Item Ordinary source program; extractor/token/proof provenance remains upstream',
        'Loaded immutable SCT, Rust CloneCOW/panic/tree/key/value/source/event codecs and store authentication remain inherited interfaces',
        'Transaction conversion, byte-key projection, big-endian count codec and actual index storage reads require source correspondence',
        'Run commit denotes applying child cache to original parent; it does not imply block seal or durable multi-store publication',
        'Returned error discard remains scoped; native Host panic/queue retry and all native controls remain separate',
        'No semantic negative-control, native or full Transfer certification credit'],
    'scope': 'Concrete per-transaction index program follows the actual body and height read. Whole enclosing success derives actual body success/cache, current height, index inspection witness and exact three NV writes applied to original parent; conversion, absent identifier, count read/decode and checked ordinal are recovered. Index preserves body V/object/event effects and queue exactly. Instantiating the qualified bound Ordinary body derives exact Item re-extraction, initially absent parent volume entry and both visible markers from the whole delivery success under explicit volume key separation. No desired successful body, index witness or target cache is a premise. Rust/proof/representation/store/native/block/durability and full Transfer remain open.'}
""".rstrip() + source[end:]
source = source.replace('EXACT_ITEM_REEXTRACTION_JOINS_ORDINARY_STORAGE_AND_DELIVERY_SOURCE', 'ORDINARY_BODY_AND_CONCRETE_TRANSACTION_INDEX_WHOLE_DELIVERY_SUCCESS')
start = source.index("plan['source_repairs'] = ")
end = source.index("\nplan['artifact_policy']", start)
source = source[:start] + "plan['source_repairs'] = 'Fresh finite source over exact bound-body and index-inspection union; shared cache/raw sources, objects and reports agree. No ancestors replayed, desired result premise or guard/audit relaxation.'" + source[end:]
source = source.replace('complete twelve-module owned root', 'complete sixteen-module owned root')
source = source.replace('BOUND_ORDINARY_AND_COMPLETE_TWELVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN', 'ORDINARY_INDEX_DELIVERY_COMPLETE_SIXTEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
source = source.replace("'fresh_audits': 12, 'inherited_audits': 162", "'fresh_audits': 6, 'inherited_audits': 221")
(ROOT / 'prepare.py').write_text(source)
handwritten = ROOT / 'handwritten/TransferOrdinaryIndexDelivery01.lean'
lean = handwritten.read_text()
names = re.findall(r'^(?:structure|inductive|def|theorem) ([A-Za-z0-9_]+)', lean, re.M)
assert len(names) == 6 and '#check' not in lean
audits = '\n'.join('set_option pp.all true in\n#check @' + n + '\n#print axioms ' + n for n in names)
lean = lean.replace('\nend ShielddSecurity.TransferOrdinaryIndexDelivery01', '\n' + audits + '\n\nend ShielddSecurity.TransferOrdinaryIndexDelivery01')
handwritten.write_text(lean)
print({'fresh_audits': len(names), 'inherited_audits': 221, 'owned_modules': 16})
