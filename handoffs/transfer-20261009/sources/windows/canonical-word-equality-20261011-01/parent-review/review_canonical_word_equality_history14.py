from pathlib import Path
import ast,json,hashlib,re,difflib
J=Path(__file__).resolve().parent;D=J/'windows-canonical-word-equality-review01';P=D/'packet01';M='TransferCanonicalWordEquality01';S=P/'source/ShielddSecurity'/(M+'.lean');final=S.read_text();q=P/'rejected-kernel/01';old=(q/'handwritten'/(M+'.lean')).read_text();assert old==(q/'project/ShielddSecurity'/(M+'.lean')).read_text()
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def regenerate(p,expected):
 nodes=ast.parse(p.read_text()).body;cut=next(i for i,n in enumerate(nodes)if isinstance(n,ast.Expr)and isinstance(n.value,ast.Call)and isinstance(n.value.func,ast.Attribute)and n.value.func.attr=='mkdir');body=[];allowed={'source','names','oldSource','old','t','start','end','a','head','proof'}
 for n in nodes[:cut]:
  if isinstance(n,ast.Assign)and all(isinstance(t,(ast.Name,ast.Tuple))for t in n.targets)and all(x.id in allowed for t in n.targets for x in ast.walk(t)if isinstance(x,ast.Name)):
   if isinstance(n.value,ast.Call)and isinstance(n.value.func,ast.Attribute)and n.value.func.attr=='read_text':assert n.targets[0].id=='old'
   else:body.append(n)
  elif isinstance(n,ast.For)and isinstance(n.iter,ast.Name)and n.iter.id=='names':body.append(n)
  elif isinstance(n,ast.AugAssign)and isinstance(n.target,ast.Name)and n.target.id=='source':body.append(n)
 assert len(body)>=4
 for n in body:
  for c in ast.walk(n):
   if isinstance(c,ast.Call):assert isinstance(c.func,ast.Attribute)and ((isinstance(c.func.value,ast.Name)and c.func.value.id in {'re','source','oldSource','old','t','head'})or(isinstance(c.func.value,ast.Call)and c.func.attr=='replace')or(isinstance(c.func.value,ast.Subscript)and isinstance(c.func.value.value,ast.Name)and c.func.value.value.id=='old'and c.func.attr=='replace'))and c.func.attr in {'findall','index','replace','split','sub'}
 env={'re':re};exec(compile(ast.Module(body=body,type_ignores=[]),str(p),'exec'),env);assert env['source']==expected and len(env['names'])==6
regenerate(P/'qualified/recipe_source.py',final);regenerate(q/'prepare_recipe.py',old)
repairs=[('      rw [packed_word_cons_division_recovers_exact_tail, packed_word_cons_division_recovers_exact_tail] at tails','      change packWords (head :: rest) / radix64 = packWords (other :: tail) / radix64 at tails\n      rw [packed_word_cons_division_recovers_exact_tail, packed_word_cons_division_recovers_exact_tail] at tails'),('    rw [leftRelation, rightRelation, Nat.mod_eq_of_lt left.canonical, Nat.mod_eq_of_lt right.canonical] at packed','    change (radix64 ^ 4 * montgomeryValue left.words) % nullifierModulus = (radix64 ^ 4 * montgomeryValue right.words) % nullifierModulus at packed\n    rw [leftRelation, rightRelation, Nat.mod_eq_of_lt left.canonical, Nat.mod_eq_of_lt right.canonical] at packed')]
repaired=old;recipe=(q/'prepare_recipe.py').read_text()
for before,after in repairs:
 assert repaired.count(before)==1 and recipe.count(before)==1;repaired=repaired.replace(before,after);recipe=recipe.replace(before,after)
assert repaired==final and recipe.replace('transfer-canonical-word-equality-owned-floor-20261011-01','transfer-canonical-word-equality-owned-floor-20261011-02')==(P/'qualified/recipe_source.py').read_text()
events=[json.loads(l)for l in(q/'events.jsonl').read_text().splitlines()];assert len(events)==2;failed=events[-1]['result'];assert failed['status']=='failed'and failed['reason']=='Lean exit 1'and 0<failed['seconds']<240;prior=json.loads((q/'plan.json').read_text());fresh=json.loads((P/'qualified/plan.json').read_text());assert prior['pressure_limits']==fresh['pressure_limits']and(q/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes();diagnostics=[l for l in(q/'runs'/('01-'+M)/'stdout.txt').read_text().splitlines()if 'error:'in l or 'warning:'in l or 'sorryAx'in l];assert diagnostics
records=[dict(kind='Original failed beta-expression rewrite attempt, unselected',result=failed,source=pin(q/'handwritten'/(M+'.lean')),diagnostics=diagnostics,all_definitions_and_theorem_contracts_unchanged=True,proof_only_repair_exact=True,exact_delta=''.join(difflib.unified_diff(old.splitlines(True),final.splitlines(True))))]
scope='Equal-width UInt64 packing injection, fixed four-word vector raw equality, canonical internal raw domain proves Montgomery mathematical value equality iff raw word equality iff exact serialized source bytes. Canonical raw bound is explicit; arbitrary raw modulo aliases excluded. Actual native private Scalar invariant/PartialEq/constant-time primitives/word selector/Clone/hash/collection/full trace bindings remain owned OPEN'
r=dict(status='PASSED',kind='Independent pure exact original source generation, repair and complete failed-attempt review',source=pin(S),fresh_reports=6,rejected=records,scope=scope,full_transfer='OPEN',native_execution='UNRUN');out=D/'semantic-source-review01.json';out.write_text(json.dumps(r,indent=2)+'\n');p=D/'endpoint-audit-review01.json';k=json.loads(p.read_text());k.update(rejected=records,semantic_scope=scope,precise_repair_review=pin(out));p.write_text(json.dumps(k,indent=2)+'\n');print(json.dumps(dict(status='PASSED',reports=6,failed_originals=1)))
