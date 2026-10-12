"""Exact canonical add arithmetic and authenticated library static row association."""
from pathlib import Path
import json,hashlib,re
J=Path(__file__).resolve().parent;G=J.parent/'shared-build-handoff';D=J/'windows-scalar-canonical-add-review01';P=D/'packet01';M='TransferScalarCanonicalAdd01';S=P/'source/ShielddSecurity'/(M+'.lean');s=S.read_text()
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
plan=json.loads((P/'qualified/plan.json').read_text());assert all(pin(S)[k]==plan['targets'][0]['source'][k]for k in ['bytes','sha256'])
assert re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',s,re.M)==re.findall(r'^#check @([^\n]+)',s,re.M)and s.count('#check @')==5
es=[json.loads(x)for x in(P/'qualified/events.jsonl').read_text().splitlines()];assert len(es)==2 and es[-1]['result']['status']=='passed'
q=P/'rejected-canonical-add-attempt01';old=(q/'handwritten'/(M+'.lean')).read_text();assert old==(q/'project/ShielddSecurity'/(M+'.lean')).read_text()
assert s.count('    exact Nat.le_refl 4\n')==2 and s.count('      exact Nat.add_sub_cancel _ _\n')==1
assert s.replace('    exact Nat.le_refl 4\n','').replace('      exact Nat.add_sub_cancel _ _\n','')==old
ev=[json.loads(x)for x in(q/'events.jsonl').read_text().splitlines()];assert len(ev)==2 and ev[-1]['result']['status']=='failed'and ev[-1]['result']['seconds']<240
assert(q/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes()
qp=json.loads((q/'plan.json').read_text());assert qp['limits']==plan['limits']and qp['pressure_limits']==plan['pressure_limits']
logs=list(q.glob('runs/*/stdout.txt'));assert len(logs)==1 and 'unsolved goals'in logs[0].read_text()and '⊢ 4 ≤ 4'in logs[0].read_text()
library=G/'handoffs/transfer-20261009/sources/windows/bounded-native-codec-20261011-01/bounded-native-codec/qualified/context/runtime-library/bls12_381-0.8.0-scalar.rs';data=library.read_bytes();assert len(data)==36086 and hashlib.sha256(data).hexdigest()=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475';text=data.decode();start=text.index('    pub const fn add(&self, rhs: &Self)');end=text.index('    /// Negates',start);body=text[start:end]
rows=re.findall(r'let \((d\d), (carry|_)\) = adc\(self\.0\[(\d)\], rhs\.0\[(\d)\], (0|carry)\);',body)
assert rows==[(f'd{i}','carry'if i<3 else'_',str(i),str(i),'0'if i==0 else'carry')for i in range(4)]
assert '(&Scalar([d0, d1, d2, d3])).sub(&MODULUS)'in body
for token in ['sourceNormalize (adcLoop 0 (left.toList.zip right.toList)).1','adcLoop carry pairs = macLoop 1 carry pairs','(left right : CanonicalScalar)','have l := left.canonical','have r := right.canonical','twice_actual_modulus_fits_four_word_radix','(adcLoop 0 (left.words.toList.zip right.words.toList)).2.toNat = 0','source_sub_and_masked_addback_equal_single_modulus_normalization','(packWords left.words.toList + packWords right.words.toList) % nullifierModulus']:assert token in s
scope='Source-shaped four-limb ADC recurrence equals the previously proved unit-multiplier MAC recurrence. Canonical operand bounds derive sum<2p<radix^4, four retained words, zero discarded carry and exact full integer sum. SourceNormalize SBB/masked-addback then derives canonical output and exact sum modulo p. No caller no-overflow/final-carry/canonical-result/desired-value premise: CanonicalScalar input representation is explicit and its private native construction remains separately owned. Exact authenticated bls12_3810.8.0 add body independently matched four ADC operands/order/carry chain/discard and sub(MODULUS). This static association and arithmetic model do not instantiate actual Rust primitives/private Scalar constructors/trait callers/library/compiler/full native trace. One entire failed attempt retained; only two reflexive length and one add-sub proof closures added, definitions/contracts/guards unchanged. No proof replay/native execution; full Transfer/combined replay OPEN.'
r=dict(status='PASSED_SOURCE_HISTORY',source=pin(S),fresh_reports=5,rejected=[dict(result=ev[-1]['result'],events=pin(q/'events.jsonl'),source=pin(q/'handwritten'/(M+'.lean')),stdout=pin(logs[0]),repair='Only explicit closure of three existing proof subgoals; unchanged definitions/contracts/guards')],native_static_association=dict(library=pin(library),add_body_sha256=hashlib.sha256(body.encode()).hexdigest(),adc_rows=rows),scope=scope,full_transfer='OPEN',native_execution='UNRUN',kind='Canonical add exact original source/history and static library shape review; no verifier');(D/'semantic-source-review01.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(status=r['status'],reports=5,matched_adc_rows=len(rows))))

