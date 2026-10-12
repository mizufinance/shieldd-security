"""Independent exact five public scalar literals, binding lines, and original pressure history."""
from pathlib import Path
import json,hashlib,re
J=Path(__file__).resolve().parent;G=J.parent/'shared-build-handoff';D=J/'windows-scalar-public-constants-review01';P=D/'packet01';M='TransferScalarPublicConstants01';S=P/'source/ShielddSecurity'/(M+'.lean');s=S.read_text()
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
plan=json.loads((P/'qualified/plan.json').read_text());assert all(pin(S)[k]==plan['targets'][0]['source'][k]for k in ['bytes','sha256'])
assert re.findall(r'^(?:inductive|def|theorem) ([A-Za-z0-9_]+)',s,re.M)==re.findall(r'^#check @([^\n]+)',s,re.M)and s.count('#check @')==6
es=[json.loads(x)for x in(P/'qualified/events.jsonl').read_text().splitlines()];assert len(es)==2 and es[-1]['result']['status']=='passed'
q=P/'prior-public-constants-attempt01';old=q/'handwritten'/(M+'.lean');assert old.read_bytes()==S.read_bytes()==(q/'project/ShielddSecurity'/(M+'.lean')).read_bytes()
qe=[json.loads(x)for x in(q/'events.jsonl').read_text().splitlines()];assert len(qe)==2 and qe[-1]['result']['status']=='failed'and qe[-1]['result']['reason']=='Physical memory pressure'and qe[-1]['result']['seconds']<240
qp=json.loads((q/'plan.json').read_text());assert qp['limits']==plan['limits']and qp['pressure_limits']==plan['pressure_limits'];assert(q/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes()
library=G/'handoffs/transfer-20261009/sources/windows/bounded-native-codec-20261011-01/bounded-native-codec/qualified/context/runtime-library/bls12_381-0.8.0-scalar.rs';data=library.read_bytes();assert len(data)==36086 and hashlib.sha256(data).hexdigest()=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475';t=data.decode()
mapping={'twoInverse':'TWO_INV','generator':'GENERATOR','rootOfUnity':'ROOT_OF_UNITY','rootOfUnityInverse':'ROOT_OF_UNITY_INV','delta':'DELTA'};modulus=52435875175126190479447740508185965837690552500527637822603658699938581184513;rinv=pow(pow(2,256,modulus),-1,modulus);constants={}
for case,name in mapping.items():
 body=re.search(r'const '+name+r': Scalar = Scalar\(\[([\s\S]*?)\]\);',t);assert body
 words=[int(x.replace('_',''),16)for x in re.findall(r'0x[0-9a-f_]+',body[1])];assert len(words)==4
 modeled=re.search(r'\| \.'+case+r' => #v\[([^\]]+)\]',s);assert modeled
 assert [int(x,16)for x in re.findall(r'0x[0-9a-f]+',modeled[1])]==words
 raw=sum(word*2**(64*i)for i,word in enumerate(words));assert raw<modulus and all(word<2**64 for word in words)
 binding='const '+('MULTIPLICATIVE_GENERATOR'if case=='generator'else name)+': Self = '+name+';';assert binding in t
 constants[name]=dict(words=words,raw_integer=str(raw),montgomery_value=str(raw*rinv%modulus),public_binding=binding)
assert int(constants['TWO_INV']['montgomery_value'])==(modulus+1)//2
assert int(constants['GENERATOR']['montgomery_value'])==7
assert int(constants['ROOT_OF_UNITY']['montgomery_value'])*int(constants['ROOT_OF_UNITY_INV']['montgomery_value'])%modulus==1
for token in ['packWords (sourceConstantWords constant).toList < nullifierModulus','⟨sourceConstantWords constant, every_source_public_constant_has_derived_canonical_raw_words constant⟩','(serializerBytes (sourceConstant constant).words.toList).length = 32','montgomeryValue (sourceConstantWords .twoInverse) = (nullifierModulus + 1) / 2','montgomeryValue (sourceConstantWords .generator) = 7']:assert token in s
scope='All five exact pinned Rust public PrimeField Scalar literals and binding lines independently match modeled four-word vectors. Kernel derives canonical raw bounds and exact32-byte canonical Montgomery keys for every modeled PublicConstant without caller bounds. Independent closed integer checks agree with named kernel certificates: TWO_INV=(p+1)/2, GENERATOR=7, ROOT_OF_UNITY times its inverse=1 modulo p. Root orders/DELTA exponent are not established here. Original pressure attempt/source/plan/runner/history preserved with unchanged source/proofs/contracts/physical guards and limits. Six original named full reports; PublicConstant five constructors/recursors separately printed final census remains owned OPEN. Actual native private construction/library/compiler/ABI/caller trace and full Transfer remain owned OPEN; no Lean replay or native execution.'
r=dict(status='PASSED_SOURCE_HISTORY',fresh_reports=6,source=pin(S),prior_attempts=[dict(result=qe[-1]['result'],source=pin(old),events=pin(q/'events.jsonl'),stdout=[pin(x)for x in q.rglob('stdout.txt')])],native_static_association=dict(library=pin(library),constants=constants),scope=scope,generated_constructor_recursors_census='OWNED_OPEN',native_execution='UNRUN',full_transfer='OPEN');out=D/'semantic-source-review01.json';assert not out.exists();out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(status=r['status'],reports=6,exact_literals=5,original_pressure_attempts=1)))
