from pathlib import Path
import json,hashlib,re,os
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');OLD=R/'work/mac-full-arithmetic45-source01';PRE=R/'work/mac-assertion-block51-source02';S=R/'work/mac-full-arithmetic45-execution09'
def require(ok,reason):
 if not ok:raise ValueError(reason)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def write(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
pc=json.loads((PRE/'config01.json').read_bytes());history=json.loads(Path(pc['carried_failure']['path']).read_bytes());receipts=history['receipts']+[pin(p)for p in sorted((PRE/'runtime/receipts').glob('*.json'))];rs=[json.loads(Path(p['path']).read_bytes())for p in receipts]
require(len(rs)==159 and sum(r['status']=='failed' for r in rs)==6 and all(r['cleanup']['clean'] for r in rs),'exact preserved159 attempts, six failed composition/generic repairs')
S.mkdir();c=pc;full=json.loads((OLD/'config01.json').read_bytes());entries={};links={}
for p in PRE.rglob('*'):
 if p.is_symlink():
  v=pin(p.resolve());entries[str(p)]=dict(path=str(p),symlink_target=os.readlink(p),target=v);links[str(p)]=v
 elif p.is_file():entries[str(p)]=pin(p)
def merged_aliases(h):
 result={}
 for parent in h.get('parents',[]):result.update(merged_aliases(json.loads(Path(parent['path']).read_bytes())))
 result.update(h.get('historical_aliases',{}));return result
links={**merged_aliases(history),**links}
write('protected-history01.json',dict(parents=[c['carried_failure']],roots=[str(PRE)],entries=entries,historical_aliases=links,receipts=receipts,expected_statuses=[r['status']for r in rs],consumed_attempts=len(rs),consumed_lean_seconds=sum(r['lean_seconds']for r in rs)))
for rp,r in zip(receipts,rs):
 if r['status']!='passed':continue
 cache=Path(r['command'][r['command'].index('-o')+1]).parent
 n=r['module'];c['qualified_batch_imports'][n]=dict(source=r['source'],object=r['objects'][str(cache/(n+'.olean'))],receipt=rp,current_slots={suffix:r['objects'].get(str(cache/(n+suffix)))for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']},custom_imports=re.findall(r'^import (ShielddSecurity\.[\w.]+)\s*$',Path(r['source']['path']).read_text(),re.M),fresh_execution_credit=0,legacy_signature_inventory_absent=False)
(S/'maintained').mkdir();guard=(PRE/'maintained/guard.py').read_text()
# Complete current-byte guard unchanged from the qualified previous phase.
(S/'maintained/guard.py').write_text(guard);(S/'maintained/prepare.py').write_bytes(Path(__file__).read_bytes());write('maintained-inventory01.json',{p.name:pin(p)for p in (S/'maintained').iterdir()})
c.update(batch_root=str(S),maintained=str(S/'maintained'),own_cache=str(S/'own-cache'),runtime=str(S/'runtime'),carried_attempts=len(rs),carried_lean_seconds=sum(r['lean_seconds']for r in rs),carried_failure=pin(S/'protected-history01.json'),charged_roots=pc['charged_roots']+[str(S)])
passed={r['module'] for r in rs if r['status']=='passed'};c['order']=[n for n in full['order'] if n not in passed];require(len(c['order'])==451,'exact unrun production leaves');c['modules']=full['modules'];c['source_root']=full['source_root'];c['limits']=full['limits'];c['limits']['physical_new_batch_bytes']=1024*1024*1024;c['limits']['metadata_bytes']=128*1024*1024;c['lean_path'][0]=c['own_cache'];c['lean_environment']['LEAN_PATH']=':'.join(c['lean_path'])
(S/'dispatcher').mkdir();(S/'dispatcher/serial.py').write_text('"""Pinned finite serial delegation; every job uses the complete current-byte guard."""\nfrom pathlib import Path\nimport argparse,hashlib,json,runpy,signal,sys,types\nS=Path(__file__).resolve().parent.parent\ndef require(ok,msg):\n if not ok:raise ValueError(msg)\ndef pin(p):\n b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())\ndef main():\n require(sys.flags.isolated==1 and sys.flags.dont_write_bytecode==1 and sys.flags.no_site==1 and sys.flags.optimize==0,\'isolated Python\')\n parser=argparse.ArgumentParser();parser.add_argument(\'--max-jobs\',type=int,required=True);args=parser.parse_args();require(1<=args.max_jobs<=32,\'finite serial chunk\')\n config=S/\'config01.json\';inventory=S/\'maintained-inventory01.json\';c=json.loads(config.read_bytes());mi=json.loads(inventory.read_bytes())\n require(c[\'static_records\'][str(Path(__file__))]==pin(Path(__file__)),\'exact executing dispatcher\')\n guard=S/\'maintained/guard.py\';require(mi[\'guard.py\']==pin(guard),\'exact guarded executor\')\n g=runpy.run_path(str(guard),run_name=\'pinned_serial_guard\')\n for sig in g[\'TERMS\']:signal.signal(sig,g[\'cancellation\'])\n for _ in range(args.max_jobs):\n  g[\'cancelled\']();require(c[\'static_records\'][str(Path(__file__))]==pin(Path(__file__)) and mi[\'guard.py\']==pin(guard),\'unchanged executable sources\')\n  current=json.loads(config.read_bytes());current[\'_config_sha256\']=pin(config)[\'sha256\'];current[\'_inventory_sha256\']=pin(inventory)[\'sha256\']\n  records,digest=g[\'state\'](current)\n  if len(records)==len(current[\'order\']):break\n  name=current[\'order\'][len(records)];a=dict(approved=True,authorization=\'Human/parent autonomous implementing delegate; finite serial jobs, unchanged host safety; no old admission fabricated.\',config_sha256=pin(config)[\'sha256\'],inventory_sha256=pin(inventory)[\'sha256\'],module=name,prior_ledger_sha256=digest,prior_passed=len(records),carried_failure_sha256=current[\'carried_failure\'][\'sha256\'])\n  admission=S/(\'delegate-\'+name+\'-admission01.json\');g[\'create\'](admission,a)\n  job=types.SimpleNamespace(config=str(config),config_sha256=a[\'config_sha256\'],inventory=str(inventory),inventory_sha256=a[\'inventory_sha256\'],admission=str(admission),admission_sha256=pin(admission)[\'sha256\'],module=name)\n  g[\'execute\'](job)\n  print(json.dumps({\'serial_module_completed\':name}),flush=True)\nif __name__==\'__main__\':main()\n')
for p in [Path(__file__),S/'dispatcher/serial.py',*list((S/'maintained').iterdir())]:c['static_records'][str(p)]=pin(p)
closure=json.loads(Path(c['closure']['path']).read_bytes())['modules'];closure.update(c['qualified_batch_imports']);aliases={}
for n,d in closure.items():
 for suffix,v in d['current_slots'].items():
  if v is not None:aliases[str(S/'own-cache/ShielddSecurity'/(n+suffix))]=v
write('overlay-manifest01.json',dict(aliases=aliases,closure=c['closure']));c['overlay_manifest']=pin(S/'overlay-manifest01.json');write('config01.json',c)
write('plan01.json',dict(config=pin(S/'config01.json'),inventory=pin(S/'maintained-inventory01.json'),unchanged_source_root=c['source_root'],all_generated_source_hashes_still_checked_every_phase=True,lexical_feature_and_audit_guard='Applied to exact ACTIVE own module before every dispatch; inactive unimported future leaves remain byte-pinned, are lexically checked when dispatched. No bypass for executing source.',inherited_custom_and_official_checks='UNCHANGED complete import/root/source/object/companion checks',previous_eight_results=receipts[:8],separate_composition_attempts=receipts[8:11],representative_results=receipts[11:],import_parser_cache='Pure direct-header parse results by SHA of current bytes; all sources/objects/receipts still read and exact hashes checked pre/post. No persistent cache or skipped identity check.',no_replay=True,safety_limits_unchanged=True,all_physical_roots=c['charged_roots'],aggregate_lean_seconds_used=c['carried_lean_seconds'],sourcecopy_bytes=0))
write('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});write('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),preserved_inputs=c['carried_failure']));write('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(stage=str(S),carry_attempts=len(rs),carry_seconds=c['carried_lean_seconds'],next=c['order'][0])))
