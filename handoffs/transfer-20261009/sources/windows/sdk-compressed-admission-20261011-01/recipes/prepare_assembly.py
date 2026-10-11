"""Prepare four sources and27 audits including qualified native arithmetic dependencies."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-codec-endpoint-20261010-01/assemble.py').read_text()
text = text.replace('Seal4scoped sources/33audits', 'Seal4scoped sources/27audits')
start = text.index('STAGES = ['); end = text.index('\n\ndef pin', start)
text = text[:start] + "STAGES = [('transfer-sdk-encoding-injective-model-20261010-02', 1),\n          ('transfer-sdk-native-nonidentity-20261010-02', 1),\n          ('transfer-sdk-native-witness-20261010-02', 1),\n          ('transfer-sdk-compressed-admission-model-20261010-03', 1)]" + text[end:]
text = text.replace('== 33\n', '== 27\n')
start = text.index('for task_name, module, classification in ['); end = text.index(']:\n    task =', start)
text = text[:start] + "for task_name, module, classification in [\n    ('transfer-sdk-encoding-injective-model-20261010-01','SDKEncodingInjective01','Missing explicit modulus argument to representative injectivity: compiler rejection'),\n    ('transfer-sdk-native-nonidentity-20261010-01','GroupNativeNonidentity','Unused zero_add simplifier argument: strict warning rejection'),\n    ('transfer-sdk-compressed-admission-model-20261010-01','SDKCompressedAdmission01','Unqualified native subgroup-witness import: rejected before compilation'),\n    ('transfer-sdk-compressed-admission-model-20261010-02','SDKCompressedAdmission01','Reserved public binder name: compiler rejection')" + text[end:]
text = text.replace("'runs/01-'+module+'/stdout.txt']]", "'runs/01-'+module+'/stdout.txt'] if (task/name).is_file()]")
text = text.replace('transfer-sdk-codec-owned-floor-20261010-01', 'transfer-sdk-native-witness-owned-floor-20261010-02')
start = text.index('for task_name,module in ['); end = text.index("check = DIAG/", start)
text = text[:start] + "for task_name,_ in STAGES:\n    for name in ['prepare_fresh.py','prepare_stage.py','predecessor_prepare_recipe.py']:\n        if (DIAG/task_name/name).exists():\n            copy(DIAG/task_name/name,'execution-context/'+task_name+'/'+name)\nfor name in ['GroupNativeNonidentity','GroupNativeSubgroupWitness']:\n    copy(Path('C:/src/shieldd-formal/circuits/ShielddSecurity')/(name+'.lean'),'inputs/prior-handwritten/'+name+'.lean')\nfor layer in ['transfer-sdk-encoding-owned-floor-20261010-01','transfer-sdk-native-nonidentity-owned-floor-20261010-02']:\n    for name in ['prepare.py','prepare_recipe.py','composition-review.json']:\n        copy(DIAG/layer/name,'owned-import-context/'+layer+'/'+name)\n" + text[end:]
text = text.replace('transfer-sdk-codec-checkpoint-20261010-02', 'transfer-sdk-compressed-admission-checkpoint-20261010-01')
text = text.replace('transfer-sdk-compressed-admission-checkpoint-20261010-01', 'transfer-sdk-compressed-admission-checkpoint-20261010-02')
text = text.replace('transfer-sdk-admission-endpoint-20261010-01', 'transfer-sdk-codec-endpoint-20261010-01')
text = text.replace('sdk-admission-parent-manifest.json', 'sdk-codec-parent-manifest.json')
text = text.replace('sdk_admission_parent_archive', 'sdk_codec_parent_archive')
text = text.replace('portable-windows-sdk-admission-endpoint01.tar.xz', 'portable-windows-sdk-codec-endpoint01.tar.xz')
text = text.replace('SCOPED_MATHEMATICAL_SDK_ITERATOR_DECODER_AND_CONCRETE_JOIN', 'SCOPED_MATHEMATICAL_SDK_ENCODING_AND_ADMISSION_NATIVE_CONSTRAINTS')
text = text.replace('6b85891f959e9aeb475945f26092f5ae7849fc5a', '389ba28b9b42012b619ea735a6ddfe8a205ec7df')
text = text.replace("'type_axiom_pairs':33", "'type_axiom_pairs':27")
start = text.index("    'scope':"); end = text.index("    'guard_delta':", start)
scope = 'Full concrete-curve compressed encoding is injective, including zero roots and torsion. Mathematical curve/encoding/modulus/nonidentity admission identifies a unique actual subgroup nonidentity point and derives all six owned native witness arithmetic constraints. SDK randomization preserves the subgroup and agrees with owned native authorization for canonical scalar casts. A separate randomized-output nonidentity gate is retained. No per-witness target equation, output subgroup, Satisfies or row/copy correspondence is assumed.'
text = text[:start] + "    'scope':" + repr(scope) + ',\n' + text[end:]
text = text.replace('portable-windows-sdk-codec-endpoint01.tar.xz\'\nwith', 'portable-windows-sdk-compressed-admission-endpoint01.tar.xz\'\nwith')
text = text.replace("'sources':4,'audits':33", "'sources':4,'audits':27")
text = text.replace("['prepare_fresh.py','prepare_stage.py','predecessor_prepare_recipe.py']", "['prepare_fresh.py','prepare_stage.py','predecessor_prepare_fresh.py','predecessor_prepare_recipe.py']")
ast.parse(text)
(ROOT / 'assemble.py').write_text(text, encoding='utf-8', newline='\n')
print('Four-source27-audit packet recipe; all qualified passes and fresh checkpoint required.')
