"""Independent source square-shift or diagonal conservation/history review; no verifier."""
from pathlib import Path
import json,hashlib,re,sys
J=Path(__file__).resolve().parent;G=J.parent/'shared-build-handoff'
label=sys.argv[1] if len(sys.argv)>1 else 'scalar-square-shift'
assert label in ['scalar-square-shift','scalar-square-diagonal']
M={'scalar-square-shift':'TransferScalarSquareShift01','scalar-square-diagonal':'TransferScalarSquareDiagonal01'}[label]
count={'scalar-square-shift':7,'scalar-square-diagonal':4}[label]
D=J/('windows-'+label+'-review01');P=D/'packet01';S=P/'source/ShielddSecurity'/(M+'.lean');s=S.read_text()
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
plan=json.loads((P/'qualified/plan.json').read_text());assert all(pin(S)[k]==plan['targets'][0]['source'][k]for k in ['bytes','sha256'])
assert re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',s,re.M)==re.findall(r'^#check @([^\n]+)',s,re.M)and s.count('#check @')==count
es=[json.loads(x)for x in(P/'qualified/events.jsonl').read_text().splitlines()];assert len(es)==2 and es[-1]['result']['status']=='passed'
def definitions(text):return [m.group(0).strip()for m in re.finditer(r'(?m)^def [\s\S]*?(?=^(?:def|theorem|set_option pp.all)|\Z)',text)]
def contracts(text):return [m.group(0).split(' := by')[0].strip()for m in re.finditer(r'(?m)^theorem [\s\S]*?(?=^(?:def|theorem|set_option pp.all)|\Z)',text)]
history=[]
for q in sorted(P.glob('prior-*')):
 sources=list((q/'handwritten').glob('*.lean')) if (q/'handwritten').exists()else[]
 for old in sources:
  assert definitions(old.read_text())==definitions(s) and contracts(old.read_text())==contracts(s)
  projected=q/'project/ShielddSecurity'/old.name
  if projected.exists():assert projected.read_bytes()==old.read_bytes()
 e=q/'events.jsonl';record=dict(attempt=q.name,sources=[pin(x)for x in sources],preparation=[pin(x)for x in q.glob('*.py')])
 if e.exists():
  events=[json.loads(x)for x in e.read_text().splitlines()];result=events[-1]['result'];assert len(events)==2 and result['status']=='failed'and result['seconds']<240
  qp=json.loads((q/'plan.json').read_text());assert qp['limits']==plan['limits']and qp['pressure_limits']==plan['pressure_limits'];assert(q/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes()
  logs=list(q.rglob('stdout.txt'));record.update(result=result,events=pin(e),stdout=[pin(x)for x in logs],diagnostics=[line for x in logs for line in x.read_text().splitlines()if 'error:'in line or 'warning:'in line])
 else:record['execution']='UNRUN_OR_SETUP_ONLY; original files preserved; no kernel result'
 history.append(record)
assert len(history)==3
library=G/'handoffs/transfer-20261009/sources/windows/bounded-native-codec-20261011-01/bounded-native-codec/qualified/context/runtime-library/bls12_381-0.8.0-scalar.rs'
data=library.read_bytes();assert len(data)==36086 and hashlib.sha256(data).hexdigest()=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475'
t=data.decode();start=t.index('    pub const fn square(&self)');body=t[start:t.index('\n    }',start)+6]
if label=='scalar-square-shift':
 old=(P/'prior-square-shift-attempt02/handwritten'/(M+'.lean')).read_text();assert old.replace('have prefix :=','have crossPrefix :=').replace('prefix.1','crossPrefix.1').replace('prefix.2','crossPrefix.2')==s
 expected=['let r7 = r6 >> 63;']+[f'let r{i} = (r{i} << 1) | (r{i-1} >> 63);'for i in range(6,1,-1)]+['let r1 = r1 << 1;']
 observed=[line.strip()for line in body.splitlines()if re.match(r'\s*let r\d+ =',line)]
 assert observed==expected
 for token in ['(word <<< 1) ||| (previous >>> 63)','| [] => [previous >>> 63]','word.toNat / 2 ^ 63','Nat.shiftLeft_add_eq_or_of_lt','packWords (sourceDoubleWalk previous words) = 2 * packWords words + (previous >>> 63).toNat','(sourceDoubleWalk 0 (sourceCrossWords self)).length = 8','2 * (radix64 * crossValue self.toList)']:assert token in s
 scope='Arbitrary UInt64 adjacent shifts and OR derive disjoint low-bit addition and full doubled-word conservation. Symbolic walk retains the top bit; actual seven-word cross input derives eight words and exact doubled cross integer, with no caller word bound or desired result. Exact pinned Rust descending assignments retain pre-shift neighbor values and match this simultaneous arithmetic interpretation. One original failed Lean attempt plus two setup-only histories preserved; reserved proof-local prefix renamed crossPrefix, all definitions/contracts/guards unchanged. Diagonal terms, terminal carry discard, reduction and native primitive/library/compiler/ABI/caller full trace remain owned OPEN.'
else:
 expected=[]
 for i in range(4):
  expected.append((f'r{2*i}','carry',f'{0 if i==0 else "r"+str(2*i)}, self.0[{i}], self.0[{i}], {0 if i==0 else "carry"}'))
  expected.append((f'r{2*i+1}', '_'if i==3 else'carry',f'0, r{2*i+1}, carry'))
 suffix=body[body.index('        let (r0, carry)'):]
 observed=re.findall(r'let \((\w+), (\w+|_)\) = (?:mac|adc)\(([^;]+)\);',suffix);assert observed==expected
 for token in ['word.toNat * word.toNat + radix64 ^ 2 * diagonalValue rest','let first := split128 (mac128 low word word carry)','let second := adc64 0 high first.2','(width : accumulated.length = 2 * words.length)','radix64 ^ (2 * words.length) * (diagonalWalk words carry accumulated).2.toNat','packWords words * packWords words = diagonalValue words + 2 * radix64 * crossValue words']:assert token in s
 scope='Symbolic diagonal MAC/ADC pair walk derives exact width and full packed integer including terminal carry, for arbitrary words/carry and internally usable matching accumulator width. Algebraically diagonal plus twice radix-scaled cross value equals packed integer square. Exact pinned Rust four diagonal MAC/ADC argument and carry chains match modeled recurrence. Two original failed attempts (physical pressure and proof errors) and one setup-only successor preserved. Program definitions and theorem contracts unchanged; distributivity and ADC zero simplifications repaired. Actual terminal carry discard/reduction/canonical square composition and native primitive/compiler/caller/full trace remain owned OPEN.'
r=dict(status='PASSED_SOURCE_HISTORY',fresh_reports=count,source=pin(S),prior_attempts=history,native_static_association=dict(library=pin(library),source_body_sha256=hashlib.sha256(body.encode()).hexdigest(),selected_operations=observed),scope=scope+' Original named full reports only; no Lean replay/native execution/full Transfer certification.',native_execution='UNRUN',full_transfer='OPEN')
out=D/'semantic-source-review01.json';assert not out.exists();out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(label=label,status=r['status'],reports=count,original_histories=len(history))))
