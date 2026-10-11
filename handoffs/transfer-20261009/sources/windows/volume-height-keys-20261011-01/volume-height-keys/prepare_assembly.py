"""Seal portable exact-ASCII source generation, key proofs and whole-call join."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
assert not (ROOT / 'assemble.py').exists()
source = (DIAG / 'transfer-ordinary-height-endpoint-20261011-01/assemble.py').read_text()
def replace(before, after):
    global source
    assert source.count(before) == 1, before
    source = source.replace(before, after)
source = source.replace('transfer-ordinary-height-source-20261011-01', 'transfer-volume-height-keys-20261011-01')
source = source.replace('transfer-ordinary-height-checkpoint', 'transfer-volume-height-keys-checkpoint')
source = source.replace('ordinary-height-endpoint', 'volume-height-keys-endpoint')
replace("MODULE = 'TransferOrdinaryHeightSource01'", "MODULE = 'TransferVolumeHeightKeys01'")
replace('assert len(fresh) == 5', 'assert len(fresh) == 9')
replace("assert pool['objects'] == 18 and len(pool['inherited_public_reports']) == 229", "assert pool['objects'] == 19 and len(pool['inherited_public_reports']) == 234")
replace("manager_endpoint = DIAG / 'transfer-ordinary-indexed-values-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-ordinary-height-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-ordinary-indexed-values-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-ordinary-height-endpoint01.tar.xz'")
replace('ccd2899c974ded96de44ff607a72a5fc8eea93df971bebecd717c0816265d24e', '3769f37fa4d3257ce66f2bfc5b9e820f78521c57a375a2478c7719c64749362a')
replace("tar.extractfile('reports/fresh-2-complete-declarations.txt')", "tar.extractfile('reports/fresh-5-complete-declarations.txt')")
replace('assert len(manager_reports) == 2', 'assert len(manager_reports) == 5')
replace("'module': 'TransferOrdinaryIndexedValues01'", "'module': 'TransferOrdinaryHeightSource01'")
replace('assert len(combined_reports) == 229', 'assert len(combined_reports) == 234')
replace('assert len(manager_selected) == 18', 'assert len(manager_selected) == 19')
replace("reference = {'indexed_values':", "reference = {'height':")
replace("'imported_complete_reports': 2},", "'imported_complete_reports': 5},")
replace("'complete_owned_modules': 18, 'inherited_complete_reports': 229", "'complete_owned_modules': 19, 'inherited_complete_reports': 234")
replace('Exact eighteen-module closure through same-action indexed values, with all 229 inherited complete reports.',
    'Exact nineteen-module closure through source height read and all-return V framing, with all 234 inherited complete reports.')
replace("add(CURRENT / ('handwritten/' + MODULE + '.lean')", "add(CURRENT / ('portable-source/' + MODULE + '.lean')")
source = source.replace('two current-overlay height read/API definitions and three finite read/decode/V-frame/whole-indexed-height proofs', 'four exact-ASCII key definitions and five finite namespace/projected-key/whole-indexed-success proofs')
replace("add(stdout, 'reports/fresh-5-complete-declarations.txt'", "add(stdout, 'reports/fresh-9-complete-declarations.txt'")
replace("add(stdout, 'reports/fresh-9-complete-declarations.txt', 'all raw full types and permitted axioms')", """add(stdout, 'reports/fresh-9-complete-declarations.txt', 'all raw full types and permitted axioms')
for name in ['generate.py', 'source.lean.in']:
    add(CURRENT / name, 'generator/' + name, 'maintained deterministic LF source generator and finite handwritten proof template')
add(CURRENT / 'generate-rejected-prefix-parser.py', 'pre-admission/generator-original.py', 'ambiguous prefix lookup refused before Lean; zero proof/control credit')
add(CURRENT / ('generated/' + MODULE + '.lean'), 'pre-admission/intermediate-source.lean', 'intermediate unadmitted newline variant; zero kernel credit')
generator_spec = importlib.util.spec_from_file_location('portable_ascii_key_generator', CURRENT / 'generate.py')
generator = importlib.util.module_from_spec(generator_spec)
generator_spec.loader.exec_module(generator)
runtime_root = Path('C:/src/shieldd-pr160-844389ee')
regenerated = generator.render((runtime_root / 'crates/core/component/sct/src/state_key.rs').read_text(),
    (runtime_root / 'crates/core/component/shielded-pool/src/state_key.rs').read_text()).encode('utf-8')
assert regenerated == (CURRENT / ('portable-source/' + MODULE + '.lean')).read_bytes()
assert b'\\r' not in regenerated""")
source = source.replace('complete eighteen-module first import root', 'complete nineteen-module first import root')
source = source.replace('verified 229 inherited reports', 'verified 234 inherited reports')
source = source.replace('WHOLE_ORDINARY_INDEXED_SUCCESS_DERIVES_ORIGINAL_PARENT_HEIGHT_FROM_CURRENT_OVERLAY_READ_QUALIFIED', 'ACTUAL_ASCII_KEY_NAMESPACE_SEPARATION_JOINS_WHOLE_ORDINARY_INDEXED_HEIGHT_AND_VOLUME_SUCCESS_QUALIFIED')
source = source.replace("'fresh_definition_audits': 2, 'fresh_theorem_audits': 3", "'fresh_definition_audits': 4, 'fresh_theorem_audits': 5")
source = source.replace("'fresh_complete_public_audits': 5", "'fresh_complete_public_audits': 9")
source = source.replace("'inherited_complete_public_audits': 229", "'inherited_complete_public_audits': 234")
start = source.index("    'scope': mapping['scope'] + ")
end = source.index("\ndump(ROOT / 'review.json', review)", start)
source = source[:start] + """    'portable_generated_bytes_verified': True,
    'pre_admission_generator_refusals': 1, 'pre_admission_kernel_credit': 0,
    'scope': mapping['scope'] + ' Nine source declarations qualified in one guarded Lean attempt. Source generator verifies the exact runtime function literals, scopes prefix extraction to volume_nullifiers, and reproduces all admitted LF bytes. Original ambiguous-prefix parser and intermediate newline variant remain preserved and unadmitted. Byte-to-model key projection remains explicit; hashes are identity evidence only, not Rust semantics, native control or certification.'}
""".rstrip() + source[end:]
source = source.replace("'fresh_audits': 5", "'fresh_audits': 9").replace("'inherited_audits': 229", "'inherited_audits': 234")
(ROOT / 'assemble.py').write_text(source)
print({'fresh_reports': 9, 'inherited_reports': 234, 'owned_modules': 19})
