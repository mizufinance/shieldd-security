"""Verify existing concrete-field certificates and exact constructor parameter identities."""
from pathlib import Path
import json,hashlib,re,subprocess
J=Path(__file__).parent;G=J.parent/'shared-build-handoff';D=J/'windows-field-reuse-review01';P=D/'packet01'
def read(p):return json.loads(p.read_bytes())
def sha(b):return hashlib.sha256(b).hexdigest()
R=read(P/'review.json');M=read(P/'manifest.json')
for e in M['files']:
 b=(P/e['path']).read_bytes();assert len(b)==e['bytes']and sha(b)==e['sha256']
for e in R['canonical_sources']:
 b=subprocess.check_output(['git','show',e['git_revision']+':'+e['git_path']],cwd=G);assert b==(P/e['path']).read_bytes();assert sha(b)==e['sha256']
receipt=read(P/'receipts/published-concrete-field.json');run=receipt['runs']['concrete01'];result=run['modules']['ConcreteJubjubField01'];audit=read(P/'original/ConcreteJubjubField01/audit.json');assert audit==result['audit'];assert result['actual_exit']==run['actual_exit']==run['root_resume_status']==int((P/'original/ConcreteJubjubField01/exit.txt').read_text())==0;assert run['recipe']==read(P/'original/recipe.json')
assert sha((P/'original/manifest.json').read_bytes())==run['manifest_sha256'];assert sha((P/'original/ConcreteJubjubField01/stdout.txt').read_bytes())==result['stdout_sha256'];assert not(P/'original/ConcreteJubjubField01/stderr.txt').read_bytes();assert sha(b'')==result['stderr_sha256']
source=(P/'original/project/ShielddSecurity/ConcreteJubjubField01.lean').read_bytes();assert source==(P/'retained/ConcreteJubjubField01.lean').read_bytes()and sha(source)==audit['candidate_sha256'];primary=(P/'source/ConcreteJubjubField01.lean').read_bytes();assert sha(primary)==audit['original_source_sha256'];assert source.decode().replace('\r\n','\n').split('\nset_option pp.all true in')[0].rstrip()==primary.decode().replace('\r\n','\n').split('\nend ShielddSecurity.ConcreteJubjubField01')[0].rstrip()
names=['ShielddSecurity.ConcreteJubjubField01.'+n for n in re.findall(r'^#check @([\w.]+)\s*$',source.decode(),re.M)];assert len(names)==10 and set(names)==set(audit['axioms'])
log=(P/'original/ConcreteJubjubField01/stdout.txt').read_text();assert not re.search(r'\b(?:warning|error|info|trace):|sorryAx',log);pos=0;reports=[]
for name in names:
 pattern=r'(?m)^@?'+re.escape(name)+r'(?:\.\{[^\n]*?\})?\s*:[\s\S]*?^\''+re.escape(name)+r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
 matches=list(re.finditer(pattern,log));assert len(matches)==1;match=matches[0];assert not log[pos:match.start()].strip();signature=match.group(0).split("\n'"+name+"' ",1)[0];assert all(not line.strip()or line[0].isspace()for line in signature.splitlines()[1:]);axioms=[a.strip()for a in(match.group(1)or'').split(',')if a.strip()];assert axioms==audit['axioms'][name]and set(axioms)<={'propext','Classical.choice','Quot.sound'};reports.append(dict(declaration=name,full_type=signature,full_type_sha256=sha(signature.encode()),axioms=axioms));pos=match.end()
assert not log[pos:].strip()
def literal(path,name,typ):
 text=(P/path).read_text();found=re.findall(r'\bdef '+re.escape(name)+r'\s*:\s*'+typ+r'\s*:=\s*(\d+)',text);assert len(found)==1;return int(found[0])
d=literal('mac/CapturedFirstSubgroup81.lean','d','Int');coefficient=literal('source/ConcreteJubjubField01.lean','coefficientNat','Nat');p=literal('mac/TransferFirstSubgroupData01.lean','p','Nat');modulus=literal('source/Scalar.lean','modulus','Nat');assert d==coefficient and p==modulus
assert R['fresh_lean_processes']==R['fresh_proof_credit']==R['fresh_runtime_controls']==0 and receipt['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
out=dict(kind='Independent review of reused original concrete-field proofs and exact source/type/parameter identities; no builds',status='PASSED',existing_reports=10,fresh_reports=0,fresh_lean_processes=0,canonical_source_records=len(R['canonical_sources']),full_declarations=reports,parameters=dict(d=d,p=p,imaginary=literal('source/ConcreteJubjubField01.lean','imaginaryNat','Nat')),application='Over ConcreteJubjubField01.F use coefficient_no_unit_square and imaginary_square; exact positive Int/Nat cast normalization and constructor application still require a Mac theorem',native_correspondence='OPEN',full_transfer='OPEN');(D/'endpoint-audit-review01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='full_declarations'}))
