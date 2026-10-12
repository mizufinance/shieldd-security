from pathlib import Path
import ast,hashlib,json
J=Path(__file__).parent;W=J.parent;old=W/'mac-full-arithmetic45-execution308/maintained/guard.py';new=W/'mac-full-arithmetic45-execution309/maintained/guard.py'
pin=lambda p:dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
assert pin(old)['sha256']=='59992e67fcf97456530454e56b07b18a4d6b11eb4580720283626f360bc16d99';assert pin(new)['sha256']=='f2693920b0a9f5e5b7a3cc0afcd72e1d2d5cad54c9211c11ab48cff50461f1b7'
prior=J/'mac-restored-disk-charge-review324.json';assert json.loads(prior.read_text())['status']=='PASSED'
a=ast.parse(old.read_text());b=ast.parse(new.read_text());names=[]
for f in a.body:
 if not isinstance(f,ast.FunctionDef):continue
 for n in ast.walk(f):
  if isinstance(n,ast.Compare) and ast.unparse(n)=='len(_CHECKED) <= 65536':n.comparators=[ast.Constant(131072)];names.append(f.name)
assert names==['checked_phase_close','fixed_check','bounds'];assert ast.dump(a,include_attributes=False)==ast.dump(b,include_attributes=False)
checks=[]
for f in b.body:
 if isinstance(f,ast.FunctionDef)and f.name in names:
  call=next(n for n in ast.walk(f)if isinstance(n,ast.Call)and ast.unparse(n).startswith('require(len(_CHECKED) <= 131072'))
  expression=compile(ast.Expression(body=call.args[0]),str(new),'eval')
  for count,expected in [(0,True),(65536,True),(65537,True),(131072,True),(131073,False)]:assert eval(expression,{'_CHECKED':range(count)})is expected
  checks.append(f.name)
report=dict(status='PASSED',baseline_guard=pin(old),successor_guard=pin(new),prior_review=pin(prior),controls=dict(sites=checks,counts=[0,65536,65537,131072,131073]),scope='Exactly three AST constants change: finite metadata identity-stamp cardinality65536→131072 at initial fixed/bounds and terminal checks. All hashing, original/archived identity stamps, link/keyset checks and final inode checks retained. Physical verifier heap/RSS/RAM/disk/process/time/thread AST unchanged; metadata caches retain their separate byte limits. Production phase308 stopped before any intent/Lean when the expanded official+retained-history identity census exceeded the former finite metadata count. Pure actual predicate boundary controls only, no production main/dispatcher/Lean or proof qualification.',full_transfer='OPEN')
out=J/'mac-identity-cardinality-review332.json';assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n');print('PASSED exact three metadata cardinality constants; all physical verifier checks identical')
