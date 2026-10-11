from pathlib import Path
import ast,hashlib,json,re
d=Path(__file__).parent;p=d/'packet01'
s=(p/'rejected/02/source.lean').read_text().split('\nset_option pp.all true in\n',1)[0]
t=ast.parse((p/'qualified/prepare_successor.py').read_text())
literal=[x for x in t.body if isinstance(x,ast.Assign) and any(isinstance(v,ast.Name) and v.id=='dispatch' for v in x.targets)]
assert len(literal)==1
dispatch=ast.literal_eval(literal[0].value)
marker='theorem index_failure_discards_child_and_consumes_queue'
assert s.count(marker)==1;s=s.replace(marker,dispatch+marker,1)
for result in ['failed','success']:
 old='  unfold flush\n  rw [nonempty_test queued nonempty, '+result+']\n  rfl\n'
 assert s.count(old)==1
 s=s.replace(old,'  rw [post_take_dispatch put height parent queued nonempty, '+result+']\n',1)
names=['ShielddSecurity.TransferDeferredQueueSourceModel01.'+n for n in re.findall(r'^(?:inductive|structure|abbrev|def|theorem) ([A-Za-z0-9_]+)',s,re.M)]
assert len(names)==17
for name in names:s+='\nset_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
expected=(p/'source/ShielddSecurity/TransferDeferredQueueSourceModel01.lean').read_bytes()
assert s.encode()==expected
out={'kind':'Source-only exact retained predecessor repair replay; original bytes unchanged; no compiler','modules':1,'declarations':17,'source_bytes':len(expected),'source_sha256':hashlib.sha256(expected).hexdigest(),'recipe_sha256':hashlib.sha256((p/'qualified/prepare_successor.py').read_bytes()).hexdigest(),'changes':'One reusable dispatch lemma and two definitional proof replacements, preserved flush semantics and existing theorem premises/conclusions.'}
(d/'successor-source-review01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
