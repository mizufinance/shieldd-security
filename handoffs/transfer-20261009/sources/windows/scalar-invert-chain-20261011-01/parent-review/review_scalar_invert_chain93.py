"""Independent original inversion generator, static chain, and repair review; no Lean."""
from pathlib import Path
import ast, hashlib, json, re, subprocess, sys
J=Path(__file__).resolve().parent; G=J.parent/'shared-build-handoff'
D=J/'windows-scalar-invert-chain-review01'; P=D/'packet01'
M='TransferScalarInvertChain01'; S=P/'source/ShielddSecurity'/(M+'.lean'); s=S.read_text()
def read(p): return json.loads(p.read_bytes())
def pin(p):
 b=p.read_bytes(); return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
plan=read(P/'qualified/plan.json')
assert all(pin(S)[k]==plan['targets'][0]['source'][k] for k in ['bytes','sha256'])
assert re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',s,re.M)==re.findall(r'^#check @([^\n]+)',s,re.M)
assert s.count('#check @')==12
es=[json.loads(x) for x in (P/'qualified/events.jsonl').read_text().splitlines()]
assert len(es)==2 and es[-1]['result']['status']=='passed'
library=G/'handoffs/transfer-20261009/sources/windows/bounded-native-codec-20261011-01/bounded-native-codec/qualified/context/runtime-library/bls12_381-0.8.0-scalar.rs'
data=library.read_bytes(); assert len(data)==36086 and hashlib.sha256(data).hexdigest()=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475'
t=data.decode(); start=t.index('    pub fn invert('); end=t.index('\n    }',start)+6; body=t[start:end]
shape=read(P/'context/scalar-invert-chain-shape.json'); assert shape['invert_body']==body
assert shape['library']['bytes']==len(data) and shape['library']['sha256']==pin(library)['sha256']
# Independently parse every source statement and compare each Lean instruction.
chain=body[body.index('        let mut t0 ='):body.index('        CtOption::new')]
statements=[line.strip() for line in chain.splitlines() if line.strip()]
assert len(statements)==shape['instruction_count']==85
rows=shape['instructions']; assert [r['original_statement'] for r in rows]==statements
values={}; derived=[]
def arg(v):
 if v=='self': return '.input',1
 index=int(v[1:]); assert index in values
 return '(.register '+str(index)+')',values[index]
for statement,row in zip(statements,rows):
 multi=re.fullmatch(r'square_assign_multi\(&mut t(\d+), (\d+)\);',statement)
 square=re.fullmatch(r'(?:let (?:mut )?)?t(\d+) = (self|t\d+)\.square\(\);',statement)
 product=re.fullmatch(r'(?:let (?:mut )?)?t(\d+) = (self|t\d+) \* &?(self|t\d+);',statement)
 inplace=re.fullmatch(r't(\d+) \*= &?(self|t\d+);',statement)
 if multi or square:
  match=multi or square; target=int(match[1]); operand='t'+str(target) if multi else match[2]; count=int(match[2]) if multi else 1
  expression,exponent=arg(operand); values[target]=exponent*2**count
  derived.append('  .square '+str(target)+' '+expression+' '+str(count))
  assert row['kind']=='square' and row['target']==target and row['count']==count
 else:
  assert product or inplace,statement
  match=product or inplace; target=int(match[1]); left=match[2] if product else 't'+str(target); right=match[3] if product else match[2]
  a,x=arg(left); b,y=arg(right); values[target]=x+y
  derived.append('  .multiply '+str(target)+' '+a+' '+b)
  assert row['kind']=='multiply' and row['target']==target
actual=s[s.index('def sourceInvertInstructions : List InvertInstruction := [\n')+len('def sourceInvertInstructions : List InvertInstruction := [\n'):s.index(']\n\ntheorem source_invert_instruction_reads_are_well_formed')]
assert actual==',\n'.join(derived)
modulus=52435875175126190479447740508185965837690552500527637822603658699938581184513
assert values[0]==modulus-2 and str(values[0])==shape['python_exponent_crosscheck']
assert sorted(values)==shape['register_indices']
assert 'CtOption::new(t0, !self.ct_eq(&Self::zero()))' in body
# Replay only reviewed pure generator with path assignments redirected to a fresh fixture.
scratch=D/'generation-replay93'; assert not scratch.exists(); scratch.mkdir()
diag=scratch/'diagnostics'; root=diag/'generator'; root.mkdir(parents=True)
fixture=diag/'transfer-bounded-native-codec-20261011-02/context/runtime-library/bls12_381-0.8.0-scalar.rs'
fixture.parent.mkdir(parents=True); fixture.write_bytes(data)
tree=ast.parse((P/'qualified/generate_source.py').read_text())
assign=next(x for x in tree.body if isinstance(x,ast.Assign) and any(isinstance(y,ast.Name) and y.id=='ROOT' for y in x.targets))
assign.value=ast.Call(func=ast.Name(id='Path',ctx=ast.Load()),args=[ast.Constant(str(root))],keywords=[])
runner=scratch/'reviewed_generator.py'; runner.write_text(ast.unparse(ast.fix_missing_locations(tree))+'\n')
done=subprocess.run([sys.executable,'-I','-B','-S',str(runner)],capture_output=True,text=True,timeout=30)
assert done.returncode==0,done.stderr
assert (root/'generated'/ (M+'.lean')).read_bytes()==S.read_bytes()
generated_shape=read(root/'context/scalar-invert-chain-shape.json')
assert {k:v for k,v in generated_shape.items() if k!='library'}=={k:v for k,v in shape.items() if k!='library'}
history=[]; prior_sources=[]
for q in sorted(P.glob('prior-invert-chain-attempt*')):
 old=q/'generated'/(M+'.lean'); assert old.read_bytes()==(q/'project/ShielddSecurity'/(M+'.lean')).read_bytes()
 qe=[json.loads(x) for x in (q/'events.jsonl').read_text().splitlines()]; result=qe[-1]['result']
 assert len(qe)==2 and result['status']=='failed' and result['seconds']<240
 qp=read(q/'plan.json'); assert qp['limits']==plan['limits'] and qp['pressure_limits']==plan['pressure_limits']
 assert (q/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes()
 logs=list(q.rglob('stdout.txt')); diagnostics=[line for log in logs for line in log.read_text().splitlines() if 'error:' in line or 'warning:' in line]
 history.append(dict(attempt=q.name,result=result,source=pin(old),generator=pin(q/'generate_source.py'),events=pin(q/'events.jsonl'),stdout=[pin(x) for x in logs],diagnostics=diagnostics))
 prior_sources.append(old.read_text())
assert len(history)==4
# First three attempts retain definitions/contracts; fourth adds finite deciders.
def strip_proof(text):
 return [match.group(0).split(' := by')[0].strip() for match in re.finditer(r'(?m)^theorem [\s\S]*?(?=^theorem |^def |^set_option pp.all|\Z)',text)]
assert all(strip_proof(old)==strip_proof(s) for old in prior_sources)
assert prior_sources[-1].replace('  | .register _ => inferInstance','  | .register index => inferInstanceAs (Decidable (index ∈ defined))')==s
for old in prior_sources[:3]:
 assert old[old.index('def sourceInvertInstructions'):old.index('\n\ntheorem source_invert_instruction_reads_are_well_formed')]==s[s.index('def sourceInvertInstructions'):s.index('\n\ntheorem source_invert_instruction_reads_are_well_formed')]
scope='Exact authenticated85 ordered source statements independently parsed against generated instruction list and pure generator replay. Original kernel proofs derive initialized reads, successful canonical payload, exact modeled zero refusal, canonical serialization, and a separate natural exponent modulus-minus-two certificate. The public final theorems take arbitrary CanonicalScalar input without caller success/bounds/final-result premises. Exponent certificate is separate from payload field-value semantics; actual exponent/inverse, native ct_eq/Choice/private Scalar/library/compiler/ABI/caller trace and full Transfer remain owned OPEN. Four original pressure/proof failures preserved with exact original histories; repair changes proof/finite deciders, not source instructions, theorem contracts, physical guards or limits. Twelve named full reports; generated InvertInstruction/Operand constructor-recursors belong to separate ancestor census. No Lean replay or native execution.'
r=dict(status='PASSED_SOURCE_HISTORY',fresh_reports=12,source=pin(S),generator=pin(P/'qualified/generate_source.py'),generator_replay=pin(root/'generated'/(M+'.lean')),native_static_association=dict(library=pin(library),invert_body_sha256=hashlib.sha256(body.encode()).hexdigest(),statements=85,final_exponent=str(values[0])),prior_attempts=history,scope=scope,native_execution='UNRUN',full_transfer='OPEN')
out=D/'semantic-source-review01.json'; assert not out.exists(); out.write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(dict(status=r['status'],reports=12,original_failed_attempts=4,source_statements=85,generator_replay='EXACT')))
