"""Prepare narrow successor recipes; complete411 floor must qualify first."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
for task, module, count, imports, scope in [
    ('transfer-sdk-sign-selection-model-20261010-01', 'SDKSignSelection01', 7,
     ['ShielddSecurity.SDKCompressedDecoder01'],
     'Mathematical sqrt-root conditional-negation and ZIP216 sign selection. A valid SDK-base square root is nonzero, and odd-sign selection gives the independently certified SDK base with no point-identity premise. Seven full audits. Actual native Rust sqrt/field/canonical-byte representation and full Transfer remain open.'),
    ('transfer-sdk-codec-join-20261010-01', 'SDKCodecJoin01', 6,
     ['ShielddSecurity.SDKByteIterator01','ShielddSecurity.SDKCompressedDecoder01','ShielddSecurity.SDKSpendAuthSubgroup01'],
     'Join the exact mathematical reverse-byte/reverse-inner-bit/skip-four loop to the concrete SDK multiplication proof, literal scalar-modulus bytes test and SDK compressed-decoder subgroup membership. Six full audits. Native Rust iterator/field/bytes/decoder correspondence and full Transfer remain open.')]:
    target = ROOT.parent / task
    text = (ROOT.parent / 'transfer-sdk-decoder-model-20261010-01/prepare_recipe.py').read_text()
    text = text.replace('SDKCompressedDecoder01',module)
    text = text.replace('len(names) == 9','len(names) == '+str(count))
    text = text.replace("'assert len(names) == 9'",repr('assert len(names) == '+str(count)))
    text = text.replace('transfer-sdk-spend-auth-owned-floor-20261010-01','transfer-sdk-codec-owned-floor-20261010-01')
    text = text.replace("floor['objects'] == 408", "floor['objects'] == 411")
    text = text.replace("\"'imports': ['ShielddSecurity.SDKSpendAuthCertificates01']\"",repr("'imports': "+repr(imports)))
    start = text.index('scope = '); end = text.index("text = text[:start]",start)
    text = text[:start]+'scope = '+repr(scope+' No runtime/BMC/control/certification credit.')+'\n'+text[end:]
    text = text.replace('MATHEMATICAL_CANONICAL_SDK_DECODER_UNIQUENESS','MATHEMATICAL_SDK_CODEC_SUCCESSOR')
    ast.parse(text)
    (target / 'prepare_recipe.py').write_text(text,encoding='utf-8',newline='\n')
    print(task,module,count,imports)
