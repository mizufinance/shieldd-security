"""Arbitrary wide-digit constructor, pinned R3, original failures and native static shape."""
from pathlib import Path
import json,hashlib,re
J=Path(__file__).resolve().parent;G=J.parent/'shared-build-handoff';D=J/'windows-scalar-wide-constructor-review01';P=D/'packet01';M='TransferScalarWideConstructor01';S=P/'source/ShielddSecurity'/(M+'.lean');s=S.read_text()
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
plan=json.loads((P/'qualified/plan.json').read_text());assert all(pin(S)[k]==plan['targets'][0]['source'][k]for k in ['bytes','sha256'])
assert re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',s,re.M)==re.findall(r'^#check @([^\n]+)',s,re.M)and s.count('#check @')==6
es=[json.loads(x)for x in(P/'qualified/events.jsonl').read_text().splitlines()];assert len(es)==2 and es[-1]['result']['status']=='passed'
records=[]
for i in [1,2]:
 q=P/f'rejected-wide-constructor-attempt{i:02d}';old=(q/'handwritten'/(M+'.lean')).read_text();assert old==(q/'project/ShielddSecurity'/(M+'.lean')).read_text()
 assert old.count('    congr 1')==1 and old.replace('    congr 1','    apply congrArg (fun value : Nat => value % nullifierModulus)')==s
 ev=[json.loads(x)for x in(q/'events.jsonl').read_text().splitlines()];assert len(ev)==2 and ev[-1]['result']['status']=='failed'and ev[-1]['result']['seconds']<240
 assert(q/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes()
 qp=json.loads((q/'plan.json').read_text());assert qp['limits']==plan['limits']and qp['pressure_limits']==plan['pressure_limits']
 logs=list(q.glob('runs/*/stdout.txt'))
 if i==1:assert ev[-1]['result']['reason']=='Physical memory pressure'and not logs
 else:assert len(logs)==1 and 'maximum recursion depth has been reached'in logs[0].read_text()
 records.append(dict(result=ev[-1]['result'],events=pin(q/'events.jsonl'),source=pin(q/'handwritten'/(M+'.lean')),stdout=pin(logs[0])if logs else None,repair='Only generic congruence tactic replaced by explicit congrArg modulo function; definitions/contracts/guards/recursion limits unchanged. Entire pressure/error attempts retained'))
library=G/'handoffs/transfer-20261009/sources/windows/bounded-native-codec-20261011-01/bounded-native-codec/qualified/context/runtime-library/bls12_381-0.8.0-scalar.rs';data=library.read_bytes();assert len(data)==36086 and hashlib.sha256(data).hexdigest()=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475';text=data.decode()
r3=re.search(r'const R3: Scalar = Scalar\(\[([^]]+)\]\);',text)[1];rust=[int(x.replace('_',''),16)for x in re.findall(r'0x[0-9a-f_]+',r3)]
lean=re.search(r'def sourceR3.*?#v\[([^]]+)\]',s,re.S)[1];assert [int(x,16)for x in re.findall(r'0x[0-9a-f]+',lean)]==rust and len(rust)==4
start=text.index('    fn from_u512(limbs: [u64; 8])');end=text.index('    /// Converts',start);body=text[start:end]
for token in ['let d0 = Scalar([limbs[0], limbs[1], limbs[2], limbs[3]])','let d1 = Scalar([limbs[4], limbs[5], limbs[6], limbs[7]])','d0 * R2 + d1 * R3']:assert token in body
for token in ['packWords sourceR3.toList = (radix64 ^ 4) ^ 3 % nullifierModulus','raw sourceR3 pinned_R3_words_have_exact_value_range_and_inverse_relation.2.1','(low high : Vector UInt64 4)','(packWords low.toList + radix64 ^ 4 * packWords high.toList) % nullifierModulus','source_four_word_radix_inverse_is_exact','source_four_adc_and_modulus_sub_preserve_canonical_modular_sum l h']:assert token in s
scope='Arbitrary two four-word raw digits are converted by actual modeled R2/R3 Montgomery multiplication then canonical add. Exact pinned R3 words, cube/range/inverse relation are kernel derived; no caller raw digit bound or operand invariant. Multiplication/addition and radix inverse contracts derive canonical wide payload and exact scalar key=(low+radix^4*high)%p. Authenticated bls12_3810.8.0 R3 bytes and from_u512 low/high index split/R2/R3 multiplication/add order independently matched. This arithmetic constructor does not bind actual eight little-endian reads/indexed array/word/private Scalar/Rust traits/compiler/callers/native trace; separate wide-byte and native correspondence remain owned OPEN. Original prelaunch memory refusal and recursion-limit proof failure retained; only a generic congruence tactic replaced by explicit modulo congrArg, definitions/contracts/physical and finite limits unchanged. No proof replay/native execution; full Transfer/combined replay OPEN.'
r=dict(status='PASSED_SOURCE_HISTORY',source=pin(S),fresh_reports=6,rejected=records,native_static_association=dict(library=pin(library),from_u512_body_sha256=hashlib.sha256(body.encode()).hexdigest(),R3_words=rust),scope=scope,full_transfer='OPEN',native_execution='UNRUN',kind='Independent wide constructor arbitrary-input premise/source/history/static R3/library shape review; no verifier');(D/'semantic-source-review01.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(status=r['status'],reports=6,rejected=len(records),R3_words=len(rust))))

