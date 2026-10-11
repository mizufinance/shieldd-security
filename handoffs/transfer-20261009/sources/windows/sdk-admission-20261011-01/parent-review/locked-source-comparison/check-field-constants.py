"""Independent source constant identities; no universal implementation proof."""
import hashlib
import json
import re
from pathlib import Path

registry = Path('/Users/antoinecyr/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
cases = [('bls12_381-0.8.0/src/scalar.rs','Scalar',52435875175126190479447740508185965837690552500527637822603658699938581184513),
         ('jubjub-0.10.0/src/fr.rs','Fr',6554484396890773809930967563523245729705921265872317281365359162392183254199)]
records = []
for relative,ty,expected in cases:
    source = registry/relative
    text = source.read_text()
    values = {}
    for constant in ['MODULUS','R','R2','R3']:
        match = re.search(r'\bconst '+constant+r': '+ty+r' = '+ty+r'\(\[(.*?)\]\);',text,re.S)
        assert match
        limbs = [int(x.replace('_',''),16) for x in re.findall(r'0x[0-9a-fA-F_]+',match.group(1))]
        assert len(limbs)==4 and all(0<=x<2**64 for x in limbs)
        values[constant] = sum(x << (64*i) for i,x in enumerate(limbs))
    assert values['MODULUS']==expected
    for constant,exponent in [('R',256),('R2',512),('R3',768)]:
        assert values[constant]==pow(2,exponent,expected)
    match = re.search(r'\bconst INV: u64 = (0x[0-9a-fA-F_]+);',text)
    assert match
    inverse = int(match.group(1).replace('_',''),16)
    assert inverse * expected % 2**64 == 2**64-1
    records.append({'source':str(source),'bytes':source.stat().st_size,
                    'sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
                    'modulus':str(expected),'modulus_bits':expected.bit_length(),
                    'constants':{key:str(value) for key,value in values.items()},'montgomery_inverse':str(inverse)})
lib = registry/'jubjub-0.10.0/src/lib.rs'
assert 'pub use bls12_381::Scalar as Fq;' in lib.read_text()
p,r = cases[0][2],cases[1][2]
assert r<p<2**255 and r<2**252
report = {'kind':'bounded source integer constant identity check',
          'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a',
          'fields':records,'fq_alias_matches':True,
          'bounds':{'r_less_than_p':True,'p_less_than_2pow255':True,'r_less_than_2pow252':True},
          'scope':'Moduli and Montgomery constants match retained formal integers. Native arithmetic/codec refinement is not established by these constant checks.',
          'kernel_replay':False,'full_transfer':'OPEN'}
target = Path(__file__).parent/'field-constant-identities01.json'
target.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'report':str(target),'fields':2,'constant_checks':10}))
