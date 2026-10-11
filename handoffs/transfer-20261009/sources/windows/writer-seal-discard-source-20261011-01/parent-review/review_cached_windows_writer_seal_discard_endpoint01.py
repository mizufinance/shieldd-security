"""Independent complete report, exact ancestry and physical guard review; no builds."""
from pathlib import Path
import json,hashlib,re,ast,difflib
J=Path(__file__).parent;W=J.parent;G=W/'shared-build-handoff';F=G/'handoffs/transfer-20261009/sources/windows/nullifier-and-raw-effects-20261011-01'
def read(p):return json.loads(p.read_bytes())
def sha(b):return hashlib.sha256(b).hexdigest()
parser=J/'windows-readback-publication-review01/verify_endpoint.py';fn=next(x for x in ast.parse(parser.read_text()).body if isinstance(x,ast.FunctionDef)and x.name=='parse');exec(compile(ast.Module(body=[fn],type_ignores=[]),str(parser),'exec'))
import argparse,subprocess
parser_args=argparse.ArgumentParser();parser_args.add_argument('pool',type=Path);parser_args.add_argument('pool_sha');parser_args.add_argument('label');parser_args.add_argument('module');parser_args.add_argument('reports',type=int);parser_args.add_argument('ancestor_reports',type=int);parser_args.add_argument('ancestor_modules',type=int);parser_args.add_argument('--output',type=Path)
a=parser_args.parse_args();assert sha(a.pool.read_bytes())==a.pool_sha
pool=read(a.pool);assert pool['full_transfer']=='OPEN'
anchor=pool['review_anchor'];assert sha(Path(anchor['path']).read_bytes())==anchor['sha256']and read(Path(anchor['path']))['status']=='PASSED'
assert subprocess.run(['git','merge-base','--is-ancestor',pool['canonical'],'HEAD'],cwd=G,capture_output=True).returncode==0
qualified={}
for key,pin in pool['original_qualification'].items():
 b=Path(pin['path']).read_bytes();assert len(b)==pin['bytes']and sha(b)==pin['sha256'];qualified[key]=json.loads(b)
accepted=read(Path(anchor['path']));originals={e['module']:e for e in qualified['owned']['selected']}
for name,e in pool['modules'].items():
 if name in originals:
  assert e['source']==originals[name]['source']and all(e['object'][k]==originals[name]['object'][k]for k in ['bytes','sha256'])
 else:
  target=qualified['plan']['targets'][0];assert name==target['module']and e['source']==target['source']and e['object']==qualified['review']['compiler_result']['objects'][0]
original_reports=dict(qualified['owned']['inherited_public_reports']);original_reports.update({e['declaration']:{k:e[k]for k in ['axioms','full_type_sha256']}for e in accepted['full_declarations']})
assert all(original_reports[name]==report for name,report in pool['reports'].items())
allreports=dict(pool['reports']);modules=dict(pool['modules'])
for name,e in modules.items():
 b=Path(e['local_reviewed_source']).read_bytes();assert len(b)==e['source']['bytes']and sha(b)==e['source']['sha256'],name
for report in allreports.values():assert set(report['axioms'])<={'propext','Classical.choice','Quot.sound'}
base={'external_floor':pool['external_floor'],'pressure_limits':pool['pressure_limits']}
tasks=[(a.label,a.module,a.reports,a.ancestor_reports,a.ancestor_modules)]
for label,module,count,ancestor_reports,ancestor_modules in tasks:
 D=J/('windows-'+label+'-review01');P=D/'packet01';M=read(P/'manifest.json');R=read(P/'review.json');plan=read(P/'qualified/plan.json');owned=read(P/'context/owned-composition-review.json');assert len(plan['targets'])==1;t=plan['targets'][0];assert t['module']==module
 for e in M['entries']:
  b=(P/e['archive_path']).read_bytes();pin=e['original'];assert len(b)==pin['bytes']and sha(b)==pin['sha256']
 b=(P/'source/ShielddSecurity'/(module+'.lean')).read_bytes();assert len(b)==t['source']['bytes']and sha(b)==t['source']['sha256'];s=b.decode();names=['ShielddSecurity.'+module+'.'+n for n in re.findall(r'^#check @([\w.]+)\s*$',s,re.M)];assert names==t['audit_names']and len(names)==count
 assert names==['ShielddSecurity.'+module+'.'+n for n in re.findall(r'^(?:noncomputable )?(?:def|abbrev|theorem|structure|inductive) ([\w.]+)',s,re.M)];assert re.findall(r'^import ([\w.]+)',s,re.M)==t['imports'];assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|axiom|unsafe|ofReduceBool|skipKernelTC)\b',s)
 events=[json.loads(l)for l in(P/'qualified/events.jsonl').read_text().splitlines()];assert len(events)==2;result=events[-1]['result'];assert result==R['compiler_result']and result['status']=='passed';log=P/('reports/fresh-'+str(count)+'-complete-declarations.txt');reports=parse(log,names,result['audits']);lb=log.read_bytes();assert len(lb)==result['stdout']['bytes']and sha(lb)==result['stdout']['sha256']
 inherited={};assert len(owned['selected'])==ancestor_modules
 for e in owned['selected']:
  old=modules[e['module']];assert e['source']==old['source'];assert all(e['object'][k]==old['object'][k]==e['copy'][k]for k in ['bytes','sha256']);prefix='ShielddSecurity.'+e['module']+'.';inherited.update({k:v for k,v in allreports.items()if k.startswith(prefix)})
 assert len(inherited)==ancestor_reports and owned['inherited_public_reports']==inherited
 assert plan['owned_imports']==[e['copy']for e in owned['selected']];assert plan['external_floor']==base['external_floor']and plan['pressure_limits']==base['pressure_limits'];assert sha((P/'qualified/execute_bounded.py').read_bytes())==pool['bounded_runner']['sha256'];assert result['seconds']<240 and result['peak_rss_bytes']<4294967296 and result['command'][1:5]==['-j1','-M1536','-DmaxHeartbeats=300000','-DmaxRecDepth=4096'];assert result['command'][-1]==t['source']['path']and result['command'][-2]==result['objects'][0]['path']
 for p in(P/'runtime').rglob('*.rs'):assert p.read_bytes()==(W/'runtime-snapshot'/p.relative_to(P/'runtime')).read_bytes()
 assert(P/'context/shieldd.lock').read_bytes()==(G/'shieldd.lock').read_bytes();pres=read(P/'preservation/preservation.json');assert pres['all_preserved']and pres['runtime_clean']and pres['runtime_head']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
 rejected=[]
 if (P/'rejected').exists() and module not in {'TransferPendingFiniteCodec01','TransferReachablePendingBlock01','TransferWriterPrepareSource01','TransferWriterSealDiscardSource01'}:
  old=(P/'rejected/source.lean').read_text();new=s.replace('\r\n','\n');contracts=lambda text:[m.group(0).split(' :=')[0]for m in re.finditer(r'(?m)^theorem [\s\S]*?(?=^theorem |^def |^set_option pp.all|\Z)',text)];definitions=lambda text:[m.group(0).strip()for m in re.finditer(r'(?m)^(?:def|abbrev|structure|inductive) [\s\S]*?(?=^(?:def|abbrev|structure|inductive|theorem|set_option pp.all)|\Z)',text)];normalized=old.replace('{api with index := fun height transaction child =>\n    asCache (executeIndex keys codec backend height transaction child)}','{api with index := (fun height transaction child =>\n    asCache (executeIndex keys codec backend height transaction child))}');assert contracts(old)==contracts(new)and definitions(normalized)==definitions(new);reject=[json.loads(l)for l in(P/'rejected/events.jsonl').read_text().splitlines()][-1]['result'];assert reject['status']=='failed';rejected.append(dict(result=reject,program_definition_delta="Only explicit indexApi lambda parentheses for IndexWriter; otherwise byte-identical definitions",all_predecessor_contracts_unchanged=True,exact_delta=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True))),diagnostics=[l for l in(P/'rejected/compiler-output.txt').read_text().splitlines()if 'error:'in l or 'warning:'in l]))
 if (P/'rejected-01').exists()and module=='TransferIndexCountCodec01':
  old=(P/'rejected-01/handwritten'/ (module+'.lean')).read_text();new=s.replace('\r\n','\n')
  contracts=lambda text:[m.group(0).split(' :=')[0]for m in re.finditer(r'(?m)^theorem [\s\S]*?(?=^theorem |^def |^set_option pp.all|\Z)',text)]
  definitions=lambda text:[m.group(0).strip()for m in re.finditer(r'(?m)^def [\s\S]*?(?=^(?:def|theorem|set_option pp.all)|\Z)',text)]
  assert len(definitions(old))==5 and len(contracts(old))==10
  normalized=old.replace('if unsafe :','if safe :').replace('unsafe.2.2','safe.2.2')
  assert contracts(old)==contracts(new)and definitions(normalized)==definitions(new)
  assert (P/'rejected-01/project/ShielddSecurity'/(module+'.lean')).read_text()==old
  reject=[json.loads(l)for l in(P/'rejected-01/events.jsonl').read_text().splitlines()][-1]['result'];assert reject['status']=='failed'
  rejected.append(dict(result=reject,program_definition_delta='Reserved binder unsafe renamed safe; all five definitions otherwise unchanged',all_predecessor_contracts_unchanged=True,exact_delta=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True))),diagnostics=[l for l in(P/'rejected-01/runs/01-TransferIndexCountCodec01/stdout.txt').read_text().splitlines()if 'error:'in l or 'warning:'in l]))
 if (P/'rejected-01').exists()and module=='TransferOrdinaryMaxCount01':
  old=(P/'rejected-01/generated'/(module+'.lean')).read_text();new=s.replace('\r\n','\n')
  contracts=lambda text:[m.group(0).split(' :=')[0]for m in re.finditer(r'(?m)^theorem [\s\S]*?(?=^theorem |^def |^set_option pp.all|\Z)',text)]
  definitions=lambda text:[m.group(0).strip()for m in re.finditer(r'(?m)^def [\s\S]*?(?=^(?:def|theorem|set_option pp.all)|\Z)',text)]
  assert len(definitions(old))==1 and len(contracts(old))==5 and definitions(old)==definitions(new)and contracts(old)==contracts(new)
  assert (P/'rejected-01/project/ShielddSecurity'/(module+'.lean')).read_text()==old
  reject=[json.loads(l)for l in(P/'rejected-01/events.jsonl').read_text().splitlines()][-1]['result'];assert reject['status']=='failed'
  rejected.append(dict(result=reject,program_definition_delta='All definitions and theorem contracts unchanged; explicit decoder projection in proof',all_predecessor_contracts_unchanged=True,exact_delta=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True))),diagnostics=[l for l in(P/'rejected-01/runs/01-TransferOrdinaryMaxCount01/stdout.txt').read_text().splitlines()if 'error:'in l or 'warning:'in l]))
 if (P/'rejected-01').exists()and module=='TransferDeferredCountWalk01':
  old=(P/'rejected-01/handwritten'/(module+'.lean')).read_text();new=s.replace('\r\n','\n')
  contracts=lambda text:[m.group(0).split(' :=')[0]for m in re.finditer(r'(?m)^theorem [\s\S]*?(?=^theorem |^def |^set_option pp.all|\Z)',text)]
  definitions=lambda text:[m.group(0).strip()for m in re.finditer(r'(?m)^def [\s\S]*?(?=^(?:def|theorem|set_option pp.all)|\Z)',text)]
  assert len(definitions(old))==1 and len(contracts(old))==3 and definitions(old)==definitions(new)and contracts(old)==contracts(new)
  assert (P/'rejected-01/project/ShielddSecurity'/(module+'.lean')).read_text()==old
  reject=[json.loads(l)for l in(P/'rejected-01/events.jsonl').read_text().splitlines()][-1]['result'];assert reject['status']=='failed'
  rejected.append(dict(result=reject,program_definition_delta='All1definition and3theorem contracts unchanged; induction proof repaired',all_predecessor_contracts_unchanged=True,exact_delta=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True))),diagnostics=[l for l in(P/'rejected-01/runs/01-TransferDeferredCountWalk01/stdout.txt').read_text().splitlines()if 'error:'in l or 'warning:'in l]))
 if (P/'rejected-01').exists()and module=='TransferDeferredCountFlush01':
  old=(P/'rejected-01/handwritten'/(module+'.lean')).read_text();new=s.replace('\r\n','\n')
  contracts=lambda text:[m.group(0).split(' :=')[0]for m in re.finditer(r'(?m)^theorem [\s\S]*?(?=^theorem |^def |^set_option pp.all|\Z)',text)]
  assert not re.findall(r'^def ',old,re.M)and len(contracts(old))==3 and contracts(old)==contracts(new)
  assert (P/'rejected-01/project/ShielddSecurity'/(module+'.lean')).read_text()==old
  reject=[json.loads(l)for l in(P/'rejected-01/events.jsonl').read_text().splitlines()][-1]['result'];assert reject['status']=='failed'
  rejected.append(dict(result=reject,program_definition_delta='No program definitions changed; all3theorem contracts unchanged; proof-only redundant simplification removed',all_predecessor_contracts_unchanged=True,exact_delta=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True))),diagnostics=[l for l in(P/'rejected-01/runs/01-TransferDeferredCountFlush01/stdout.txt').read_text().splitlines()if 'error:'in l or 'warning:'in l]))
 for rejected_name in ['rejected-predecessor','rejected-second-predecessor']:
  RP=P/rejected_name
  if not RP.exists():continue
  old=(RP/'handwritten'/(module+'.lean')).read_text();new=s.replace('\r\n','\n')
  contracts=lambda text:[m.group(0).split(' :=')[0]for m in re.finditer(r'(?m)^theorem [\s\S]*?(?=^theorem |^def |^set_option pp.all|\Z)',text)]
  definitions=lambda text:[m.group(0).strip()for m in re.finditer(r'(?m)^def [\s\S]*?(?=^(?:def|theorem|set_option pp.all)|\Z)',text)]
  assert definitions(old)==definitions(new)and contracts(old)==contracts(new),(module,rejected_name)
  assert (RP/'project/ShielddSecurity'/(module+'.lean')).read_text()==old
  reject=[json.loads(l)for l in(RP/'events.jsonl').read_text().splitlines()][-1]['result'];assert reject['status']=='failed'
  rejected.append(dict(result=reject,program_definition_delta='All program definitions and theorem contracts unchanged; proof-only repair',all_predecessor_contracts_unchanged=True,exact_delta=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True))),diagnostics=[l for l in(RP/'runs'/('01-'+module)/'stdout.txt').read_text().splitlines()if 'error:'in l or 'warning:'in l]))
 if (P/'withdrawn-unrun-setup').exists():
  U=P/'withdrawn-unrun-setup';assert not list(U.rglob('events.jsonl'))
  old=(U/'handwritten'/(module+'.lean')).read_text();assert definitions(old)==definitions(new)and contracts(old)==contracts(new)
  rejected.append(dict(kind='Withdrawn unexecuted source/preparation; zero whole-attempt qualification',program_definition_delta='Same program definitions and theorem contracts',exact_delta=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True)))))
 if module in {'TransferPendingFiniteCodec01','TransferReachablePendingBlock01','TransferWriterPrepareSource01','TransferWriterSealDiscardSource01'}:
  new=s.replace('\r\n','\n')
  for RP in sorted((P/'rejected').iterdir()):
   if RP.name.startswith('stopped-sealer-setup'):
    assert {x.name for x in RP.iterdir()}=={'assemble.py','prepare_assembly.py'} and not list(RP.rglob('events.jsonl'))
    rejected.append(dict(attempt=RP.name,kind='Unexecuted sealer packaging setup; no compiler attempt qualification'))
    continue
   source_directory='handwritten'if module in {'TransferPendingFiniteCodec01','TransferWriterPrepareSource01','TransferWriterSealDiscardSource01'}else'generated'
   old=(RP/source_directory/(module+'.lean')).read_text();assert (RP/'project/ShielddSecurity'/(module+'.lean')).read_text()==old
   if module=='TransferPendingFiniteCodec01':
    normalized=old.replace('  rw [members]\n  cases pending\n  rfl\n','  rw [members]\n')
   elif module=='TransferWriterSealDiscardSource01':
    normalized=old.replace('by simpa only [interrupted, committed]','by simp only [interrupted, committed]')
   elif module=='TransferWriterPrepareSource01':
    normalized=old
    for left,right in [('backend.height state >>=','(backend.height state).bind'),('TransferPreparedAcceptedSource01.prepare backend.store previous.nullifiers height blockId accepted >>=','(TransferPreparedAcceptedSource01.prepare backend.store previous.nullifiers height blockId accepted).bind'),('backend.stageBoundary state insertions >>=','(backend.stageBoundary state insertions).bind'),('backend.prepareApplication staged >>=','(backend.prepareApplication staged).bind')]:normalized=normalized.replace(left,right)
    normalized=normalized.replace('locked, rfl, rfl, rfl, exactFrozen.symm','locked, stored, stage, application, exactFrozen.symm')
   else:
    normalized=old.replace('  · have frozenCoherent :=','  · change ensureSealed decode (project TransferNullifierObjectKeys01.nullifierBytes) ⟨sealedState, (empty : Cache O Unit)⟩ = .ok ()\n    have frozenCoherent :=')
    normalized=normalized.replace('    simp only [ensureSealed, apply_empty, stored, roundtrip _ frozenCoherent, freeze, if_true]', '    have encodedSealed : (decode (encode (freeze (parentPending decode project final.1)))).sealed = true :=\n      congrArg Pending.sealed (roundtrip (freeze (parentPending decode project final.1)) frozenCoherent)\n    simp only [ensureSealed, apply_empty, stored, encodedSealed, if_true]')
   assert normalized==new,(module,RP.name)
   events=[json.loads(l)for l in(RP/'events.jsonl').read_text().splitlines()];assert len(events)==2
   failed=events[-1]['result'];assert failed['status']=='failed'and failed['reason']==('Lean error/placeholder output'if module=='TransferWriterSealDiscardSource01'else'Lean exit 1');assert (RP/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes()
   logs=list(RP.rglob('stdout.txt'));assert len(logs)==1
   if module=='TransferWriterSealDiscardSource01':assert 'warning:'in logs[0].read_text() and 'simpa'in logs[0].read_text()
   rejected.append(dict(attempt=RP.name,result=failed,program_definition_delta='Declaration contracts and intended branch programs preserved; writer explicitly spells four Option.bind operations and uses derived call observations, other modules repair ensure goal/equality or redundant proof steps only',all_predecessor_contracts_unchanged=True,exact_delta=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True))),diagnostics=[l for l in logs[0].read_text().splitlines()if 'error:'in l or 'warning:'in l]))
 out=dict(status='PASSED',kind='Independent complete type/source/runtime/ancestor/guard review; no Lean/native execution',fresh_modules=1,fresh_reports=count,inherited_reports=ancestor_reports,full_declarations=reports,custom_imports=owned['selected'],manifest_entries=len(M['entries']),guard_unchanged=True,rejected=rejected,interfaces=R['interfaces'],scope=R['scope'],full_transfer='OPEN')
 if True:
  out['ancestry_cache']={'path':str(a.pool),'sha256':a.pool_sha,'review_anchor':anchor,'scope':'Previously independently accepted exact associations, not fresh replay'}
  output=a.output or D/'endpoint-audit-review01.json';assert not output.exists();output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(module=module,status='PASSED',fresh=count,inherited=ancestor_reports,owned=ancestor_modules)))
 allreports.update({e['declaration']:{k:e[k]for k in ['axioms','full_type_sha256']}for e in reports});assert module not in modules;modules[module]=dict(source=t['source'],object=result['objects'][0])
