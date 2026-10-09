from pathlib import Path
import hashlib,json,re,sys
batch=Path(sys.argv[1]);m=json.loads((batch/'manifest.json').read_text(encoding='utf-8-sig'));total=0
for module,names in m['expected_theorems_by_module'].items():
 leaf=batch/module;assert (leaf/'end.txt').exists() and (leaf/'exit.txt').read_text().strip()=='0' and not (leaf/'stop.txt').exists()
 source=batch/'project'/m['sources'][module]['lean_relative_path'];assert hashlib.sha256(source.read_bytes()).hexdigest()==m['audited_candidates'][module]
 output=(leaf/'stdout.txt').read_text(encoding='utf-8-sig');stderr=(leaf/'stderr.txt').read_text(encoding='utf-8-sig');assert not re.search(r'\b(sorryAx|error)\b',output+stderr)
 reports=re.findall(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]",output)
 reports += [(n,'') for n in re.findall(r"'([\w.]+)' does not depend on any axioms",output)]
 assert len(reports)==len(names),(module,len(reports),len(names))
 used_names=set()
 for short in names:
  matches=[(full,used) for full,used in reports if full==short or full.endswith('.'+short)]
  assert len(matches)==1,(module,short,matches)
  full,used=matches[0];assert set(re.findall(r'[\w.]+',used)) <= {'propext','Classical.choice','Quot.sound'},(module,full,used)
  assert re.search(r'(?:^|\n)@?'+re.escape(full)+r'\s*:',output),'full type missing'
  used_names.add(full)
 assert len(used_names)==len(names)
 result={'audits':len(names),'full_types_checked':True,'axioms':{n:re.findall(r'[\w.]+',u) for n,u in reports},'original_source_sha256':m['sources'][module]['sha256'],'candidate_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'full_transfer':'OPEN'}
 (leaf/'audit.json').write_text(json.dumps(result,indent=2)+'\n');total+=len(names)
print(json.dumps({'audits':total,'scoped_root_audits':len(m['expected_theorems_by_module']['ConcreteWeierstrassPoint01']),'dependency_replay_audits':total-len(m['expected_theorems_by_module']['ConcreteWeierstrassPoint01']),'full_transfer':'OPEN'}))
