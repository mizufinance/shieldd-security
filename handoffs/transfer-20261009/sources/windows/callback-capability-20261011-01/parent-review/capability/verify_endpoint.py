"""Independent capability re-extraction source and complete original association review."""
from pathlib import Path
import json,re,hashlib,ast,difflib
J=Path(__file__).parent;P=J/'packet01';W=J.parent.parent;G=W/'shared-build-handoff';F=G/'handoffs/transfer-20261009/sources/windows/nullifier-and-raw-effects-20261011-01'
def read(p):return json.loads(p.read_bytes())
def sha(b):return hashlib.sha256(b).hexdigest()
parser=J.parent/'windows-readback-publication-review01/verify_endpoint.py';fn=next(n for n in ast.parse(parser.read_text()).body if isinstance(n,ast.FunctionDef)and n.name=='parse');exec(compile(ast.Module(body=[fn],type_ignores=[]),str(parser),'exec'))
M=read(P/'manifest.json');R=read(P/'review.json');plan=read(P/'qualified/plan.json');ref=read(P/'context/inherited-reference.json');owned=read(P/'context/owned-composition-review.json')
for e in M['entries']:
 b=(P/e['archive_path']).read_bytes();pin=e['original'];assert len(b)==pin['bytes']and sha(b)==pin['sha256']
assert len(plan['targets'])==1;t=plan['targets'][0];b=(P/'source/ShielddSecurity/TransferCapabilitySource01.lean').read_bytes();assert len(b)==t['source']['bytes']and sha(b)==t['source']['sha256']
s=b.decode();names=['ShielddSecurity.TransferCapabilitySource01.'+n for n in re.findall(r'^#check @([\w.]+)\s*$',s,re.M)];assert names==t['audit_names']and len(names)==11
assert names==['ShielddSecurity.TransferCapabilitySource01.'+n for n in re.findall(r'^(?:def|theorem|structure|inductive) ([\w.]+)',s,re.M)]
assert re.findall(r'^import ([\w.]+)',s,re.M)==t['imports']==['ShielddSecurity.TransferRawEffectsSource01'];assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|axiom|unsafe|ofReduceBool|skipKernelTC)\b',s)
events=[json.loads(l)for l in(P/'qualified/events.jsonl').read_text().splitlines()];assert len(events)==2;result=events[-1]['result'];assert result==R['compiler_result']and result['status']=='passed'
reports=parse(P/'reports/fresh-11-complete-declarations.txt',names,result['audits']);log=(P/'reports/fresh-11-complete-declarations.txt').read_bytes();assert len(log)==result['stdout']['bytes']and sha(log)==result['stdout']['sha256']
base=read(F/'parent-review/raw-predecessor/endpoint-audit-review01.json');corrected=read(F/'parent-review/fee-funding-successor/endpoint-audit-review01.json');inherited=dict(read(F/'raw-predecessor/context/owned-composition-review.json')['inherited_public_reports']);inherited.update({e['declaration']:{k:e[k]for k in ['axioms','full_type_sha256']}for e in corrected['full_declarations']});assert len(inherited)==84 and owned['inherited_public_reports']==inherited
oldowned=read(F/'fee-funding-successor/context/owned-composition-review.json')['selected'];assert len(owned['selected'])==5
for e in owned['selected']:
 n=e['module']
 if n=='TransferRawEffectsSource01':
  src=F/'fee-funding-successor/source/ShielddSecurity/TransferRawEffectsSource01.lean';ob=read(F/'fee-funding-successor/review.json')['compiler_result']['objects'][0];assert all(e['source'][k]==dict(bytes=src.stat().st_size,sha256=sha(src.read_bytes()))[k]for k in ['bytes','sha256'])
 else:
  old=next(x for x in oldowned if x['module']==n);assert e['source']==old['source'];ob=old['object']
 assert all(e['object'][k]==ob[k]==e['copy'][k]for k in ['bytes','sha256'])
assert plan['owned_imports']==[e['copy']for e in owned['selected']]
cp=read(F/'fee-funding-successor/qualified/plan.json');assert plan['external_floor']==cp['external_floor']and plan['pressure_limits']==cp['pressure_limits'];assert(P/'qualified/execute_bounded.py').read_bytes()==(F/'fee-funding-successor/qualified/execute_bounded.py').read_bytes()
assert result['seconds']<240 and result['peak_rss_bytes']<4294967296 and result['command'][1:5]==['-j1','-M1536','-DmaxHeartbeats=300000','-DmaxRecDepth=4096'];assert result['command'][-1]==t['source']['path']and result['command'][-2]==result['objects'][0]['path']
for f in(P/'runtime').rglob('*.rs'):assert f.read_bytes()==(W/'runtime-snapshot'/f.relative_to(P/'runtime')).read_bytes()
assert(P/'context/shieldd.lock').read_bytes()==(G/'shieldd.lock').read_bytes();pres=read(P/'preservation/preservation.json');assert pres['all_preserved']and pres['runtime_clean']and pres['runtime_head']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
old=(P/'rejected/source.lean').read_text();new=s.replace('\r\n','\n')
contracts=lambda text:[m.group(0).split(' :=')[0]for m in re.finditer(r'(?m)^theorem [\s\S]*?(?=^theorem |^def |^set_option pp.all|\Z)',text)];assert contracts(old)==contracts(new)
definitions=lambda text:[m.group(0).strip()for m in re.finditer(r'(?m)^(?:def|structure|inductive) [\s\S]*?(?=^(?:def|structure|inductive|theorem|set_option pp.all)|\Z)',text)];assert definitions(old)==definitions(new)
reject=[json.loads(l)for l in(P/'rejected/events.jsonl').read_text().splitlines()][-1]['result'];assert reject['status']=='failed'
out=dict(kind='Independent full declaration/source/import/runtime/unchanged guard review; no new Lean/native execution',fresh_modules=1,fresh_reports=11,full_declarations=reports,inherited_reports=84,manifest_entries=len(M['entries']),custom_imports=owned['selected'],guard_unchanged=True,rejected=dict(result=reject,program_definitions_and_theorem_contracts_unchanged=True,exact_delta=''.join(difflib.unified_diff(old.splitlines(True),s.replace('\r\n','\n').splitlines(True))),diagnostics=[l for l in(P/'rejected/compiler-output.txt').read_text().splitlines()if 'error:'in l or 'warning:'in l]),interfaces=R['interfaces'],scope=R['scope'],full_transfer='OPEN')
(J/'endpoint-audit-review01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in ['full_declarations','custom_imports','rejected','interfaces','scope']}))
