"""Prepare one immutable16-source172-audit packet only after all qualified passes."""
import ast
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parent
selection = json.loads((ROOT / 'selection.json').read_text())
text = (ROOT.parent / 'transfer-sdk-compressed-admission-endpoint-20261010-01/assemble.py').read_text()
text = text.replace('Seal4scoped sources/27audits', 'Seal16scoped sources/172audits')
start = text.index('STAGES = ['); end = text.index('\n\ndef pin', start)
text = text[:start] + 'STAGES = ' + repr([tuple(s) for s in selection['stages']]) + text[end:]
text = text.replace('len(entries) == 4 and len({e[\'module\'] for e in entries}) == 4',
                    'len(entries) == 16 and len({e[\'module\'] for e in entries}) == 16')
text = text.replace('== 27\n', '== 172\n')
start = text.index('for task_name, module, classification in ['); end = text.index(']:\n    task =', start)
text = text[:start] + "for task_name, module, classification in [\n    ('transfer-sdk-native-spend-auth-20261010-01','SDKNativeSpendAuth01','Missing explicit standard coordinate premise and Option-match reduction: compiler rejection'),\n    ('transfer-sdk-raw-point-multiply-20261010-01','ShielddNativeReadPoint','Unused checked simp argument: strict warning rejection'),\n    ('transfer-sdk-raw-authorization-join-20261010-01','SDKRawAuthorization01','Order lemma selected instead of additive-group negation identity: compiler rejection')" + text[end:]
text = text.replace('transfer-sdk-native-witness-owned-floor-20261010-02', 'transfer-sdk-raw-authorization-floor-20261010-01')
start = text.index('for task_name,_ in STAGES:\n    for name in'); end = text.index('check = DIAG/', start)
replacement = """for task_name,_ in STAGES:
    copied_names = {'prepare.py','prepare_recipe.py','plan.json','review.json','events.jsonl','execute_bounded.py'}
    for path in sorted((DIAG/task_name).iterdir()):
        if path.is_file() and ((path.suffix == '.py' and path.name not in copied_names) or path.name == 'source-review.json'):
            copy(path,'execution-context/'+task_name+'/'+path.name)
    review_path = DIAG/task_name/'source-review.json'
    if review_path.exists():
        for record in json.loads(review_path.read_text()):
            if 'prior_handwritten' in record:
                module = record['module']
                relative = 'inputs/prior-handwritten/'+module+'.lean'
                if not (packet/relative).exists():
                    copy(record['prior_handwritten']['path'],relative)
for layer in ['transfer-sdk-native-witness-owned-floor-20261010-02',
              'transfer-sdk-program-owned-floor-20261010-01',
              'transfer-sdk-owned-program-floor-20261010-01',
              'transfer-sdk-native-spend-auth-floor-20261010-02',
              'transfer-sdk-raw-point-multiply-floor-20261010-01',
              'transfer-sdk-raw-codec-floor-20261010-01']:
    for path in sorted((DIAG/layer).iterdir()):
        if path.is_file() and (path.suffix == '.py' or path.name == 'composition-review.json'):
            copy(path,'owned-import-context/'+layer+'/'+path.name)
for layer in ['transfer-sdk-raw-route-refresh-20261010-01','transfer-sdk-raw-route-refresh-20261010-02']:
    copy(DIAG/layer/'prepare.py','recipes/'+layer+'/prepare.py')
"""
text = text[:start] + replacement + text[end:]
text = text.replace('transfer-sdk-compressed-admission-checkpoint-20261010-02', 'transfer-sdk-raw-authorization-checkpoint-20261010-01')
text = text.replace('transfer-sdk-codec-endpoint-20261010-01', 'transfer-sdk-compressed-admission-endpoint-20261010-01')
text = text.replace('sdk-codec-parent-manifest.json', 'sdk-compressed-admission-parent-manifest.json')
text = text.replace('sdk_codec_parent_archive', 'sdk_compressed_admission_parent_archive')
text = text.replace('portable-windows-sdk-codec-endpoint01.tar.xz', 'portable-windows-sdk-compressed-admission-endpoint01.tar.xz')
text = text.replace('SCOPED_MATHEMATICAL_SDK_ENCODING_AND_ADMISSION_NATIVE_CONSTRAINTS', 'SCOPED_CONCRETE_SDK_RAW_AUTHORIZATION_ENDPOINT')
text = text.replace("'source_files':4,'handwritten_sources':4", "'source_files':16,'handwritten_sources':16")
text = text.replace("'type_axiom_pairs':27", "'type_axiom_pairs':172")
text = text.replace('389ba28b9b42012b619ea735a6ddfe8a205ec7df', selection['latest_parent_canonical_sha'])
start = text.index("    'scope':"); end = text.index("    'guard_delta':", start)
scope = 'Independent SDK base has certified exact prime order; full-curve compressed roundtrip includes zero roots and torsion. Globally coordinate-bound standard SpendAuth identifies that base, deriving exact order and actual owned scalar-one reader result without an exact-order premise. Owned raw Scalar/reader/private scalar/encoder/Point/authorization source programs compose with production SDK randomization and admitted output supplies all six native witness arithmetic constraints. Global byte-array encoding meaning derives SDK injectivity/coherence and identifies mathematical admitted key subgroup/nonidentity without an abstract decoder subgroup law. A concrete admitted nonidentity key cancels to identity with scalar one, demonstrating the separate output gate. All remaining Rust/FFI primitive/byte/coordinate correspondence contracts and original circuit rows/copies/final Transfer replay are explicit OPEN obligations.'
text = text[:start] + "    'scope':" + repr(scope) + ',\n' + text[end:]
text = text.replace('Four runner bodies', 'Nine runner bodies')
text = text.replace("copy(ROOT/'prepare_assembly.py','recipes/prepare_assembly.py')", "copy(ROOT/'prepare_assembly.py','recipes/prepare_assembly.py')\ncopy(ROOT/'selection.json','recipes/selection.json')")
text = text.replace("archive=ROOT/'portable-windows-sdk-compressed-admission-endpoint01.tar.xz'", "archive=ROOT/'portable-windows-sdk-raw-authorization-endpoint01.tar.xz'")
text = text.replace("'sources':4,'audits':27", "'sources':16,'audits':172")
runtime_context = """runtime_context = json.loads((ROOT/'runtime-context.json').read_text())
assert runtime_context['runtime_sha'] == '844389ee069e1fb2e576708842d0b389b4d9a44a'
assert runtime_context['semantic_correspondence_credit'] == 0
for record in runtime_context['files']:
    path = ROOT/'runtime-context'/record['relative_path']
    assert pin(path)['sha256'] == record['sha256'] and pin(path)['bytes'] == record['bytes']
    copy(path,'source-provenance/runtime/'+record['relative_path'])
copy(ROOT/'runtime-context.json','source-provenance/runtime-context.json')
copy(ROOT/'prepare_runtime_context.py','recipes/prepare_runtime_context.py')
"""
text = text.replace("copy(Path(__file__),'recipes/assemble.py')", runtime_context + "copy(Path(__file__),'recipes/assemble.py')")
ast.parse(text)
assert not (ROOT / 'assemble.py').exists()
(ROOT / 'assemble.py').write_text(text, encoding='utf-8', newline='\n')
print('Sixteen-source172-audit raw native endpoint assembly recipe prepared; all qualified passes/final checkpoint required.')
