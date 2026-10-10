from pathlib import Path
import sys,json,hashlib,subprocess,shutil,os
assert sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site
P=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/mac-poseidon-call1-plan14');V=P/'parent-final-call14-review01';F=P/'final-two-result06';M=P/'final-two-math-plan06'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ident=lambda p:{'bytes':p.stat().st_size,'sha256':sha(p)}
manifest=json.loads((F/'final-result-manifest06.json').read_bytes());before={Path(e['path']):ident(Path(e['path'])) for e in manifest['entries'].values()}
for name in ['final-result-manifest06.json','append-only-envelope06.json','postseal-guard06.json']:before[F/name]=ident(F/name)
target=V/'publication-source-replay02';tmp=target.with_name(target.name+'.pending');assert not target.exists() and not tmp.exists();tmp.mkdir()
recipe=json.loads((P/'successor-source03/byte-replay03.json').read_bytes())['command'];recipe[recipe.index('--output-dir')+1]=str(tmp/'source03/ShielddSecurity');recipe[recipe.index('--metadata-dir')+1]=str(tmp/'source03/metadata')
r=subprocess.run(recipe,capture_output=True,text=True,timeout=300);assert r.returncode==0 and not r.stderr,(r.returncode,r.stderr)
inp=json.loads((M/'generation-input06.json').read_bytes());root=tmp/'math06';inp['allowed_output_roots']=[str(root)]
inputpath=tmp/'parent-generation-input06.json';inputpath.open('x').write(json.dumps(inp,indent=2)+'\n')
inv=M/'maintained-inventory06.json'
# The SOURCE-only replay changes only the permitted output location, preserving all mathematical inputs.
command=['/opt/homebrew/bin/python3','-I','-B','-S',str(M/'maintained/generate_final_two06.py'),'--inventory',str(inv),'--inventory-sha256',sha(inv),'--input',str(inputpath),'--input-sha256',sha(inputpath),'--output-root',str(root)]
rr=subprocess.run(command,capture_output=True,text=True,timeout=120);assert rr.returncode==0 and not rr.stderr,(rr.returncode,rr.stderr)
selected=tmp/'selected/ShielddSecurity';selected.mkdir(parents=True);records={};receiptpaths=[]
for key,e in manifest['entries'].items():
 if not key.startswith('raw-local-only/') or not key.endswith('.json'):continue
 rp=Path(e['path']);receipt=json.loads(rp.read_bytes())
 if not isinstance(receipt,dict) or receipt.get('status')!='passed' or 'module' not in receipt or 'command' not in receipt:continue
 name=receipt['module'];assert name not in records
 actual=Path(receipt['command'][-1]);assert sha(actual)==receipt['source_sha256'] and actual.stat().st_size==receipt['source_bytes']
 if name in ['TransferPoseidonCall14Proof01','TransferPoseidonCall14CheckedControls01']:replayed=root/'ShielddSecurity'/(name+'.lean')
 elif name in ['TransferPoseidonCall14B0R00Data01','TransferPoseidonCall14B0R00Column1Probe01']:replayed=P/'successor-source02/accepted-probes'/(name+'.lean')
 else:replayed=tmp/'source03/ShielddSecurity'/(name+'.lean')
 assert replayed.read_bytes()==actual.read_bytes(),name
 dest=selected/(name+'.lean');shutil.copyfile(replayed,dest);assert ident(dest)==ident(actual)
 records[name]={'actual_source':str(actual),'actual_receipt':str(rp),'actual_receipt_sha256':sha(rp),'replay_source':str(replayed),'selected_path':str(target/'selected/ShielddSecurity'/(name+'.lean')),**ident(actual),'audit_count':receipt['axiom_audits']};receiptpaths.append(rp)
assert len(records)==57 and sum(v['audit_count'] for v in records.values())==398
assert not any(n in records for n in ['TransferPoseidonCall14Checked01','TransferPoseidonCall14Controls01'])
assert all(ident(p)==v for p,v in before.items())
# Atomic selection is DATA only, no import elaboration or kernel replay.
report={'status':'PASS_57_ACCEPTED_SOURCES_EXACT_BYTE_REPLAY','selected_modules':57,'retained_actual_type_STD_pairs':398,'source03_generator_stdout':r.stdout,'source03_command':recipe,'math06_command':command,'source03_generator_sha256':sha(P/'successor-source03/maintained/generate_successors.py'),'math06_generator_sha256':sha(M/'maintained/generate_final_two06.py'),'math06_original_input_sha256':sha(M/'generation-input06.json'),'math06_replay_input_sha256':sha(inputpath),'math06_only_input_change':'allowed_output_roots','records':records,'new_Lean_runs':0,'new_proof_credit':0,'publication_admitted':False,'actual_final_Opus_review':'PENDING_QUOTA_RESET','no_old_standalone_Checked_Controls_selected':True,'final185_entry_seal_unchanged':True,'original60_intents_exhausted':True,'full_Transfer':'OPEN'}
(tmp/'replay-selection01.json').open('x').write(json.dumps(report,indent=2)+'\n')
os.rename(tmp,target)
(V/'parent-final-source-replay02.json').open('x').write(json.dumps({'status':report['status'],'selection':str(target/'replay-selection01.json'),'selection_sha256':sha(target/'replay-selection01.json'),'modules':57,'audits':398,'new_Lean_runs':0,'review_pending':True,'full_Transfer':'OPEN'},indent=2)+'\n')
print(json.dumps({'status':report['status'],'modules':57,'audits':398,'selection_sha256':sha(target/'replay-selection01.json'),'new_Lean_runs':0}))

