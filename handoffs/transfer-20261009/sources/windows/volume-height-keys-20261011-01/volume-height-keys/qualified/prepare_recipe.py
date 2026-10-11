"""Admit finite exact-key proof emitted by checked Rust-literal generator."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
assert not (ROOT / 'prepare.py').exists()
source = (DIAG / 'transfer-ordinary-height-source-20261011-01/prepare.py').read_text()
def replace(before, after):
    global source
    assert source.count(before) == 1, before
    source = source.replace(before, after)
replace("UPSTREAM = DIAG / 'transfer-ordinary-indexed-values-20261011-01'", "UPSTREAM = DIAG / 'transfer-ordinary-height-source-20261011-01'")
source = source.replace('transfer-ordinary-height-owned-floor-20261011-01', 'transfer-volume-height-keys-owned-floor-20261011-01')
source = source.replace("MODULE = 'TransferOrdinaryHeightSource01'", "MODULE = 'TransferVolumeHeightKeys01'")
source = source.replace('TransferOrdinaryIndexedValues01', 'TransferOrdinaryHeightSource01')
replace('assert len(current) == 2', 'assert len(current) == 5')
replace('assert len(records) == 18 and len(audits) == 229', 'assert len(records) == 19 and len(audits) == 234')
replace("'objects': 18", "'objects': 19")
source = source.replace('Complete eighteen-module first owned root; 229 inherited full reports.', 'Complete nineteen-module first owned root; 234 inherited full reports.')
replace("handwritten = ROOT / 'handwritten' / (MODULE + '.lean')", "handwritten = ROOT / 'portable-source' / (MODULE + '.lean')")
replace('assert len(names) == 5', 'assert len(names) == 9')
start = source.index("prior_mapping = json.loads((UPSTREAM / 'source-mapping.json').read_bytes())")
end = source.index("\nmapping_file = ROOT / 'source-mapping.json'", start)
source = source[:start] + """prior_mapping = json.loads((UPSTREAM / 'source-mapping.json').read_bytes())
key_files = [runtime / 'crates/core/component/sct/src/state_key.rs', runtime / 'crates/core/component/shielded-pool/src/state_key.rs']
generator_spec = importlib.util.spec_from_file_location('exact_key_generator', ROOT / 'generate.py')
generator = importlib.util.module_from_spec(generator_spec)
generator_spec.loader.exec_module(generator)
assert handwritten.read_bytes() == generator.render(key_files[0].read_text(), key_files[1].read_text()).encode('utf-8')
runtime_union = {}
for row in prior_mapping['runtime_sources'] + [pin(p) for p in key_files]:
    assert pin(row['path']) == row
    assert row['path'] not in runtime_union or runtime_union[row['path']] == row
    runtime_union[row['path']] = row
mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_union.values()),
    'generator': pin(ROOT / 'generate.py'), 'template': pin(ROOT / 'source.lean.in'),
    'source_literals': {'height': 'sct/block_manager/block_height', 'entry_prefix': 'shielded_pool/volume_nullifiers/entries/', 'day_prefix': 'shielded_pool/volume_nullifiers/days/'},
    'interfaces': prior_mapping['interfaces'] + ['Byte-to-Nat equality-preserving projection remains explicit; arbitrary suffixes include all actual day/nullifier encodings without proving those codecs'],
    'scope': 'Checked runtime function literals emit exact ASCII height/entry/day prefixes. Finite source-key proofs derive byte namespace separation for arbitrary appended suffixes, and projected height/volume and entry/day separation from explicit representation injectivity. Whole same-action indexed success now derives exact Item re-extraction, initial volume-entry absence, both visible volume markers, original encoded height/decoder observation and preserved final height with no separate key-separation premises. Equality-preserving model key projection, stateless extractor/token/proof/Rust/store/tree/native/block/durability remain interfaces. An ambiguous-prefix generator refusal before source admission has zero Lean, proof or negative-control credit. Full Transfer remains open.'}
""".rstrip() + source[end:]
replace("plan['pins'] += mapping['runtime_sources'] + [plan['lean'], plan['external_floor'], plan['preservation']]",
    "plan['pins'] += mapping['runtime_sources'] + [plan['lean'], plan['external_floor'], plan['preservation']]\nplan['pins'] += [pin(ROOT / n) for n in ['generate.py', 'source.lean.in', 'generate-rejected-prefix-parser.py', 'generated/TransferVolumeHeightKeys01.lean']]")
source = source.replace('CURRENT_VIEW_HEIGHT_GETTER_DERIVED_FROM_WHOLE_ORDINARY_INDEX_SUCCESS', 'ACTUAL_ASCII_VOLUME_HEIGHT_KEY_SEPARATION_JOINS_WHOLE_INDEXED_SUCCESS')
start = source.index("plan['source_repairs'] = ")
end = source.index("\nplan['artifact_policy']", start)
source = source[:start] + "plan['source_repairs'] = 'Fresh portable generated source derives checked runtime ASCII namespace separation. Pre-admission ambiguous prefix parser refused before Lean; original parser and intermediate source retained with zero kernel credit. Generator scopes volume namespace and emits LF bytes reproducibly. No generated source hand edit, ancestor replay or guard/audit relaxation.'" + source[end:]
source = source.replace('complete eighteen-module owned root', 'complete nineteen-module owned root')
source = source.replace('ORDINARY_HEIGHT_COMPLETE_EIGHTEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN', 'VOLUME_HEIGHT_KEYS_COMPLETE_NINETEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
source = source.replace("'fresh_audits': 5, 'inherited_audits': 229", "'fresh_audits': 9, 'inherited_audits': 234")
(ROOT / 'prepare.py').write_text(source)
print({'fresh_audits': 9, 'inherited_audits': 234, 'owned_modules': 19, 'pre_admission_generator_refusal_credit': 0})
