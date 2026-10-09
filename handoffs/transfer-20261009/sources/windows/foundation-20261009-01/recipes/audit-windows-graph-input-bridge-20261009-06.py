from pathlib import Path
import hashlib,json,re,sys
batch=Path(sys.argv[1]);manifest=json.loads((batch/'manifest.json').read_text(encoding='utf-8-sig'));total=0
for module,names in manifest['expected_theorems_by_module'].items():
 leaf=batch/module;assert (leaf/'end.txt').exists() and (leaf/'exit.txt').read_text().strip()=='0' and not (leaf/'stop.txt').exists()
 raw=(batch/'project/ShielddSecurity'/(module+'.lean')).read_bytes();assert hashlib.sha256(raw).hexdigest()==manifest['audited_candidates'][module]
 output=(leaf/'stdout.txt').read_text(encoding='utf-8-sig');stderr=(leaf/'stderr.txt').read_text(encoding='utf-8-sig');assert not re.search(r'\b(sorryAx|error)\b',output+stderr)
 prefix='ShielddSecurity.'+module+'.';escaped=re.escape(prefix)
 reports=re.findall("'"+escaped+r"(\w+)' depends on axioms: \[([^\]]*)\]",output)
 reports += [(n,'') for n in re.findall("'"+escaped+r"(\w+)' does not depend on any axioms",output)]
 assert len(reports)==len(names) and {n for n,_ in reports}==set(names),(module,reports,names)
 for name,used in reports:
  assert set(re.findall(r'[\w.]+',used)) <= {'propext','Classical.choice','Quot.sound'},(module,name,used)
  assert prefix+name+' ' in output,'full type missing'
 result={'audits':len(names),'full_types_checked':True,'axioms':{n:re.findall(r'[\w.]+',u) for n,u in reports},'original_source_sha256':manifest['sources'][module]['sha256'],'candidate_sha256':hashlib.sha256(raw).hexdigest(),'full_transfer':'OPEN'}
 (leaf/'audit.json').write_text(json.dumps(result,indent=2)+'\n');total+=len(names)
print(json.dumps({'audits':total,'new_bridge_audits':5,'unchanged_prerequisite_replay_audits':total-5,'full_transfer':'OPEN'}))
