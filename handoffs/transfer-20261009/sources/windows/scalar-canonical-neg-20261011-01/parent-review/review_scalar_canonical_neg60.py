"""Canonical negation zero/nonzero proof, retained pressure history and static library shape."""
from pathlib import Path
import json,hashlib,re
J=Path(__file__).resolve().parent;G=J.parent/'shared-build-handoff';D=J/'windows-scalar-canonical-neg-review01';P=D/'packet01';M='TransferScalarCanonicalNeg01';S=P/'source/ShielddSecurity'/(M+'.lean');s=S.read_text()
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
plan=json.loads((P/'qualified/plan.json').read_text());assert all(pin(S)[k]==plan['targets'][0]['source'][k]for k in ['bytes','sha256'])
assert re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',s,re.M)==re.findall(r'^#check @([^\n]+)',s,re.M)and s.count('#check @')==6
es=[json.loads(x)for x in(P/'qualified/events.jsonl').read_text().splitlines()];assert len(es)==2 and es[-1]['result']['status']=='passed'
records=[]
for i in [1,2]:
 q=P/f'rejected-canonical-neg-attempt{i:02d}';old=(q/'handwritten'/(M+'.lean')).read_text();assert old==(q/'project/ShielddSecurity'/(M+'.lean')).read_text()
 expected=old.replace('have head := Nat.eq_zero_of_add_eq_zero_left zero','have head : word.toNat = 0 := by omega').replace('have product := Nat.eq_zero_of_add_eq_zero_right zero','have product : radix64 * packWords rest = 0 := by omega').replace('.resolve_left (by decide)','.resolve_left (by decide : radix64 ≠ 0)')
 assert expected==s
 ev=[json.loads(x)for x in(q/'events.jsonl').read_text().splitlines()];assert len(ev)==2 and ev[-1]['result']['status']=='failed'and ev[-1]['result']['seconds']<240
 assert(q/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes()
 qp=json.loads((q/'plan.json').read_text());assert qp['limits']==plan['limits']and qp['pressure_limits']==plan['pressure_limits']
 logs=list(q.glob('runs/*/stdout.txt'))
 if i==1:assert len(logs)==1 and 'Expected type must not contain metavariables'in logs[0].read_text()
 else:assert old==s and ev[-1]['result']['reason']=='Physical memory pressure'and not logs
 records.append(dict(result=ev[-1]['result'],events=pin(q/'events.jsonl'),source=pin(q/'handwritten'/(M+'.lean')),stdout=pin(logs[0])if logs else None,repair='Only explicit local natural-number proof facts/radix annotation; unchanged definitions/contracts/limits'if i==1 else'Exact unchanged source and prelaunch physical pressure stop; no partial reports'))
library=G/'handoffs/transfer-20261009/sources/windows/bounded-native-codec-20261011-01/bounded-native-codec/qualified/context/runtime-library/bls12_381-0.8.0-scalar.rs';data=library.read_bytes();assert len(data)==36086 and hashlib.sha256(data).hexdigest()=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475';text=data.decode();start=text.index('    pub const fn neg(&self)');end=text.index('\n}\n',start);body=text[start:end]
sbb=re.findall(r'let \((d\d), (borrow|_)\) = sbb\(MODULUS\.0\[(\d)\], self\.0\[(\d)\], (0|borrow)\);',body)
assert sbb==[(f'd{i}','borrow'if i<3 else'_',str(i),str(i),'0'if i==0 else'borrow')for i in range(4)]
mask='let mask = (((self.0[0] | self.0[1] | self.0[2] | self.0[3]) == 0) as u64).wrapping_sub(1);'
assert mask in body and 'Scalar([d0 & mask, d1 & mask, d2 & mask, d3 & mask])'in body
for token in ['orWalk seed words = 0 ↔ seed = 0 ∧ packWords words = 0','(if orWalk 0 words = 0 then (1 : UInt64) else 0) - 1','sourceNegMask words = if packWords words = 0 then 0 else 0xffff_ffff_ffff_ffff','have noBorrow : difference.2 = false','Nat.le_of_lt scalar.canonical','(nullifierModulus - packWords scalar.words.toList) % nullifierModulus','Nat.mod_self']:assert token in s
scope='Source-shaped OR recurrence derives exact packed-word zero detection, wrapping UInt64 Boolean cast/subtract derives mask0 at zero and allones otherwise. Canonical input bound derives no final borrow in modulus-minus-input SBB recurrence; four masked output limbs are canonical and equal (p-input)%p. Zero case explicitly gives0, avoiding noncanonical p. No caller zero-mask/no-borrow/canonical-output/desired-value premise; input CanonicalScalar representation and its private native construction remain separately owned. Exact authenticated bls12_3810.8.0 neg body independently matched all four SBB operands/borrow chain/discard, four-word OR Boolean cast/wrapping_sub and final limb masks. Static source association/arithmetic model do not instantiate actual Rust primitives/private Scalar/traits/compiler/full native execution. Original proof failure and exact-source prelaunch memory refusal retained in entirety, local proof annotation repairs only; unchanged definitions/contracts/guards/physical limits. No proof replay/native execution; full Transfer/combined replay OPEN.'
r=dict(status='PASSED_SOURCE_HISTORY',source=pin(S),fresh_reports=6,rejected=records,native_static_association=dict(library=pin(library),neg_body_sha256=hashlib.sha256(body.encode()).hexdigest(),sbb_rows=sbb,mask=mask),scope=scope,full_transfer='OPEN',native_execution='UNRUN',kind='Independent canonical negation original source/history and static library association review; no verifier');(D/'semantic-source-review01.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(status=r['status'],reports=6,rejected=len(records),sbb_rows=len(sbb))))

