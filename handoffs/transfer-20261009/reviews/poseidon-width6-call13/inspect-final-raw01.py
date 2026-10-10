import hashlib,json,re
from pathlib import Path
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');P=R/'work/parent-call2-admission13';S=R/'work/mac-poseidon-width6-call2-13/successor-source05';K=R/'outputs/mac-poseidon-width6-call2-13/kernel-successors01';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();v=json.loads((S/'source-inventory01.json').read_text());selected={}
for n in v['successor_topological_order']:
 passes=[p for p in K.glob(f'build-{n}-*.json') if (r:=json.loads(p.read_text()))['status']=='passed' and r.get('fresh_credit')==1]
 assert len(passes)==1;selected[n]=passes[0]
for n,e in v['accepted_probes'].items():selected[n]=R/e['receipt_path']
assert len(selected)==45
structured=[];audit_count=0;resources=[]
for module,p in selected.items():
 r=json.loads(p.read_text());assert r['status']=='passed' and r['exit']==0
 source=S/'project/ShielddSecurity'/(module+'.lean');obj=S/'project/.lake/build/lib/lean/ShielddSecurity'/(module+'.olean')
 assert sha(source)==r['source_sha256']==v['modules'][module]['sha256'];assert sha(obj)==r['object_sha256']
 log=p.with_suffix('.log');assert sha(log)==r['log_sha256'];text=log.read_text()
 assert 'sorryAx' not in text and not re.search(r'\berror(?::|\()',text)
 names=re.findall(r'^#check @?(\S+)',source.read_text(),re.M);axiom_names=re.findall(r'^#print axioms (\S+)',source.read_text(),re.M);assert names==axiom_names and len(names)==len(set(names))
 reports=list(re.finditer(r"(?m)^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\r?$",text));assert [x.group(1) for x in reports]==names
 for name,report in zip(names,reports):
  header=list(re.finditer(r'(?m)^@?'+re.escape(name)+r'\s*:',text));assert len(header)==1 and header[0].start()<report.start()
  full=text[header[0].start():report.start()].strip();assert hashlib.sha256(full.encode()).hexdigest()==r['full_signature_sha256'][name]
  axioms=[] if not report.group(2) else [x.strip() for x in report.group(2).split(',')];assert len(axioms)==len(set(axioms)) and set(axioms)<={'propext','Quot.sound','Classical.choice'}
  structured.append({'module':module,'declaration':name,'full_type':full,'axioms':axioms,'receipt_sha256':sha(p),'raw_log_sha256':sha(log)})
 audit_count+=len(names);assert r['axiom_audits']==len(names)
 assert r['seconds']<=240 and r['peak_group_rss_bytes']<=4294967296 and r['minimum_memory_free_percent']>=15 and r['minimum_disk_free_bytes']>=2147483648
 resources.append({k:r[k] for k in ['module','seconds','peak_group_rss_bytes','minimum_memory_free_percent','minimum_disk_free_bytes']})
records=[json.loads(p.read_text()) for p in K.glob('build-*.json')];assert len(records)==45 and sum(r['status']=='failed' for r in records)==2
used=sum(r.get('seconds',0) for r in records if r.get('command_started'))+6.871448499994585;assert len(records)+2==47 and used<1200
assert audit_count==247
(P/'parent-final-raw-audits01.json').write_text(json.dumps(structured,indent=2)+'\n');(P/'parent-final-resources01.json').write_text(json.dumps(resources,indent=2)+'\n')
report={'status':'passed','accepted_modules':45,'full_type_axiom_pairs':247,'all_stage_attempts':47,'failures':2,'failed_credit':0,'unchanged_accepted_replays':0,'used_ALLstage_Lean_wall_seconds':used,'remaining_attempts':13,'remaining_wall_seconds':1200-used,'maximum_sampled_RSS_bytes':max(r['peak_group_rss_bytes'] for r in resources),'minimum_memory_free_percent':min(r['minimum_memory_free_percent'] for r in resources),'minimum_disk_free_bytes':min(r['minimum_disk_free_bytes'] for r in resources),'fullTransfer':'OPEN','publication_acceptance_pending':True}
with (P/'parent-final-raw-inspection01.json').open('x') as h:json.dump(report,h,indent=2);h.write('\n')
print(json.dumps(report))
