from pathlib import Path
import hashlib,json,re,tarfile
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
def pin(p):
    p=Path(p);b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
runtime=Path('C:/src/shieldd-pr160-844389ee');lock=(runtime/'Cargo.lock').read_text()
subtleLock=re.search(r'\[\[package\]\]\nname = "subtle"\nversion = "2.6.1"\nsource = "[^"]+"\nchecksum = "([0-9a-f]{64})"',lock).group(1)
archive=Path('C:/Users/acyrn/.cargo/registry/cache/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1.crate')
assert pin(archive)['sha256']==subtleLock=='13c2bddecc57b384dee18652358fb23172facb8a2c51ccc10d74c157bdea3292'
original=Path('C:/Users/acyrn/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs')
with tarfile.open(archive,'r:gz') as tar:assert tar.extractfile('subtle-2.6.1/src/lib.rs').read()==original.read_bytes()
text=original.read_text()
for exact in ['debug_assert!((input == 0u8) | (input == 1u8));','let mask = -(choice.unwrap_u8() as to_signed_int!($t)) as $t;','a ^ (mask & (a ^ b))','*self ^= mask & (*self ^ *other);']:
    assert exact in text
scalar=DIAG/'transfer-bounded-native-codec-20261011-02/context/runtime-library/bls12_381-0.8.0-scalar.rs'
assert pin(scalar)['sha256']=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475'
(ROOT/'context').mkdir();(ROOT/'context/subtle-2.6.1-lib.rs').write_bytes(original.read_bytes())
context={'subtle_locked_archive':pin(archive),'locked_cargo_manifest':pin(runtime/'Cargo.lock'),'subtle_source_original':pin(original),'subtle_source_copy':pin(ROOT/'context/subtle-2.6.1-lib.rs'),'scalar_source':pin(scalar),'actual_Choice_from_u8_check':'debug_assert only; byte0/1 is a documented input contract, not inferred merely from the Rust type','scope':'Exact locked subtle2.6.1 UInt64 xor/negative-mask conditional select/assign and Scalar four-word selection source values. Valid Choice byte0/1 explicit for general callers; actual modeled source power shift/mask cast derives it. Boolean branch versus masked word selection and whole source pow loop correspondence. Rust compiler/volatile barrier/ct_eq/all caller origins/timing/full Transfer remain open.'}
(ROOT/'context/scalar-choice-masks-shape.json').write_text(json.dumps(context,indent=2,sort_keys=True)+'\n')
s=(DIAG/'transfer-scalar-pow-field-20261012-08/prepare.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-scalar-pow-field-owned-floor-20261012-08'","POOL = DIAG / 'transfer-scalar-pow-field-owned-floor-20261012-08'").replace("MODULE = 'TransferScalarPowField01'","MODULE = 'TransferScalarChoiceMasks01'")
s=s.replace('assert not (ROOT / \'plan.json\').exists() and not POOL.exists()','assert not (ROOT / \'plan.json\').exists() and POOL.exists()')
start=s.index('POOL.mkdir()');end=s.index('handwritten = ROOT',start)
reuse="""composition_file=POOL/'composition-review.json'
composition=json.loads(composition_file.read_bytes())
assert composition['objects']==163 and composition['inherited_public_reports']==audits
assert len(records)==len(composition['selected'])
selected=composition['selected']
for name,source,obj in records:
    row=next(item for item in selected if item['module']==name)
    assert row['source']==source and row['object']==obj
    for key in ['source','object','copy']:assert pin(row[key]['path'])==row[key]
    inputs += [source,obj]
"""
s=s[:start]+reuse+s[end:]
s=s.replace('assert len(names) == 6','assert len(names) == 20').replace("'fresh_audits': 6","'fresh_audits': 20")
s=s.replace('scalar_pow_field_source_shape','scalar_choice_masks_source_shape').replace('scalar-pow-field-shape.json','scalar-choice-masks-shape.json')
s=s.replace("'imports': ['ShielddSecurity.TransferScalarFieldValues01', 'ShielddSecurity.TransferScalarPowBitInteger01']","'imports': ['ShielddSecurity.TransferScalarPowBitInteger01']")
start=s.index("mapping['scope'] =");end=s.index('\n',start)
s=s[:start]+"mapping['scope'] = json.loads((ROOT/'context/scalar-choice-masks-shape.json').read_text())['scope']"+s[end:]
start=s.index("unrunPower=DIAG/");end=s.index("plan['artifact_policy']",start);s=s[:start]+s[end:]
extra="""plan['pins'].append(pin(ROOT/'context/subtle-2.6.1-lib.rs'))
choiceContext=json.loads((ROOT/'context/scalar-choice-masks-shape.json').read_text())
plan['pins'] += [choiceContext[key] for key in ['subtle_locked_archive','locked_cargo_manifest','subtle_source_original','subtle_source_copy','scalar_source']]
"""
at=s.index("plan['artifact_policy']");s=s[:at]+extra+s[at:]
s=s.replace('SCALAR_POW_FIELD_COMPLETE_WORD_BRANCH_SELF_REVIEWED_UNRUN','SCALAR_CHOICE_MASKS_COMPLETE_WORD_BRANCH_SELF_REVIEWED_UNRUN')
s=s.replace('One source and bounded reports/object; complete163-module qualified word root','One source and bounded reports/object; existing exact163-module qualified word root reused without new copies')
(ROOT/'prepare.py').write_text(s)
print({'locked_subtle_archive_and_source_exact':True,'public_declarations':20,'same_complete163_module_word_pool_reused_readonly':True,'all_execution_guards_unchanged':True})
