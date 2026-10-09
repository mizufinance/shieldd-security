from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, sys

repo=Path('C:/src/shieldd-transfer-windows-publication-20261009')
local=Path('C:/src/shieldd-transfer-handoffs')
diag=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
base=repo/'handoffs/transfer-20261009'
stem='windows-connected-subgroup-semantics-20261009-03'
root='TransferFirstSubgroupSemantics01'
prepared=diag/(stem+'-source'); kernel=diag/(stem+'-kernel')
boundary=diag/'safe-connected-subgroup-semantics-boundary-2026100903'
dest=base/'sources/windows/connected-subgroup-semantics-20261009-02'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
write=lambda p,v:p.write_bytes((json.dumps(v,indent=2)+'\n').encode())
for location in [kernel,boundary]:
    assert (location/'complete.txt').exists() and (location/'end.txt').exists()
    assert (location/'exit.txt').read_text().strip()=='0'
assert (boundary/'resume-status.txt').read_text().strip()=='0'
m=load(kernel/'manifest.json')
assert m['parent_commit']=='d7d44ca82712a35a3e40d68af7ae89b25b128ce6'
phase=sys.argv[1]
if phase=='sources':
    assert not dest.exists();dest.mkdir(parents=True)
    files={}
    def copy(p,rel):
        target=dest/rel;target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(p.read_bytes())
        files[rel]={'sha256':sha(target),'bytes':target.stat().st_size}
    copy(prepared/(root+'.lean'),'circuits/ShielddSecurity/'+root+'.lean')
    assert sha(prepared/(root+'.lean'))==sha(repo/'circuits/ShielddSecurity'/(root+'.lean'))
    copy(prepared/'manifest.json','inputs/manifest.json')
    for p in [local/('prepare-'+stem+'.py'),local/('run-safe-'+stem+'.ps1'),
              local/'prepare-windows-connected-subgroup-semantics-20261009-02.py',
              local/'make-connected-semantic-preparer-20261009-02.py',
              local/'make-connected-semantic-preparer-20261009-03.py',Path(__file__),
              local/'inventory-transfer-semantic-families-20261009-01.py',
              diag/('root-'+stem+'.ps1'),diag/('audit-'+stem+'.py')]:
        copy(p,'recipes/'+p.name)
    failed_stem='windows-connected-subgroup-semantics-20261009-02'
    for p in [diag/(failed_stem+'-source')/(root+'.lean'),
              diag/(failed_stem+'-source/manifest.json'),
              local/('run-safe-'+failed_stem+'.ps1'),diag/('root-'+failed_stem+'.ps1')]:
        copy(p,'failed02/'+p.name)
    closure=dict(m['sources'])
    for item in m['reused']:
        closure[item['name']]={'sha256':item['original_source_sha256']}
    resolution={}
    for name,identity in closure.items():
        candidates=[repo/'circuits/ShielddSecurity'/(name+'.lean'),
          base/'sources/windows/maintained-review-20261009-01/formal/circuits/ShielddSecurity'/(name+'.lean'),
          base/'sources/mac/mac-connected-subgroup01/final01/project/ShielddSecurity'/(name+'.lean'),
          base/'sources/windows/subgroup-arithmetic-20261009-01/circuits/ShielddSecurity'/(name+'.lean'),
          base/'sources/windows/foundation-20261009-01/circuits/ShielddSecurity'/(name+'.lean')]
        matches=[p for p in candidates if p.exists() and sha(p)==identity['sha256']]
        assert matches,(name,'published exact source needed')
        resolution[name]={'path':str(matches[0].relative_to(repo)).replace('\\','/'),'sha256':identity['sha256']}
    write(dest/'dependency-resolution.json',resolution)
    files['dependency-resolution.json']={'sha256':sha(dest/'dependency-resolution.json'),'bytes':(dest/'dependency-resolution.json').stat().st_size}
    write(dest/'manifest.json',{'files':files,'parent_commit':m['parent_commit'],'runtime_sha':m['runtime_sha'],
       'scope':m['scope'],'full_transfer':'OPEN','generated_sources_changed':False,
       'audited_root_theorems':13,'unique_new_theorems':3,'completion_conclusion_strengthened':True})
    print(json.dumps({'files':len(files),'manifest_sha256':sha(dest/'manifest.json'),'closure':len(resolution)}))
elif phase=='verify-index':
    for rel,identity in load(dest/'manifest.json')['files'].items():
        name=str((dest/rel).relative_to(repo)).replace('\\','/')
        assert hashlib.sha256(subprocess.check_output(['git','-C',str(repo),'show',':'+name])).hexdigest()==identity['sha256']
    name='circuits/ShielddSecurity/'+root+'.lean'
    assert hashlib.sha256(subprocess.check_output(['git','-C',str(repo),'show',':'+name])).hexdigest()==sha(prepared/(root+'.lean'))
    print('Exact source Git index bytes PASS')
elif phase=='receipts':
    source_commit=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip()
    modules={}
    for name in m['order']:
        leaf=kernel/name;audited=load(leaf/'audit.json')
        assert (leaf/'end.txt').exists() and (leaf/'exit.txt').read_text().strip()=='0' and not (leaf/'stop.txt').exists()
        assert sha(kernel/'project/ShielddSecurity'/(name+'.lean'))==m['audited_candidates'][name]==audited['candidate_sha256']
        assert audited['full_types_checked']
        for axioms in audited['axioms'].values():assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
        modules[name]={'audit':audited,'actual_exit':0,'stdout_sha256':sha(leaf/'stdout.txt'),'stderr_sha256':sha(leaf/'stderr.txt')}
    total=sum(item['audit']['audits'] for item in modules.values())
    r={'runtime_sha':m['runtime_sha'],'parent_commit':m['parent_commit'],'source_commit':source_commit,
       'source_packet_manifest_sha256':sha(dest/'manifest.json'),'source_index_exact_bytes_verified':True,
       'source_commit_diff_check_exit':int(sys.argv[2]),
       'preparation_manifest_sha256':sha(kernel/'manifest.json'),'recipe':load(kernel/'recipe.json'),
       'fresh_modules':len(modules),'total_audits':total,'root_audits':13,'unique_new_root_theorems':3,
       'root_replay_audits':10,'fresh_dependency_audits':total-13,'qualified_reused_modules':len(m['reused']),
       'modules':modules,'actual_exit':0,'root_resume_status':0,'scope':m['scope'],
       'global_order_premise':'forall represented:J, (8*Scalar.order) smul represented=0',
       'outside_witness_input_preservation':'forall input<22735, input<11 or18<=input implies rho(3+input)=remaining(input)',
       'external_cache_before_sha256':sha(kernel/'external-before.json'),'external_cache_identity_rechecked':True,
       'start':(kernel/'start.txt').read_text().strip(),'end':(kernel/'end.txt').read_text().strip(),
       'failed_attempt_02':{'reason':'redundant Nat multiplication rewrite after mul_nsmul',
         'proof_and_control_credit':0,'root_resumed_status':0,
         'source_manifest_sha256':sha(diag/'windows-connected-subgroup-semantics-20261009-02-source/manifest.json'),
         'root_stdout_sha256':sha(diag/'windows-connected-subgroup-semantics-20261009-02-kernel'/root/'stdout.txt')},
       'full_transfer':'OPEN','native_successors':'UNRUN','new_negative_control_credit':0}
    p=base/'receipts/windows/connected-subgroup-concrete-20261009-02.json';assert not p.exists();write(p,r)
    inventory=base/'reviews/windows-semantic-family-inventory-20261009-01.json'
    inv=load(inventory);inv['checked_instance']['coverage02_successor']={'receipt':str(p.relative_to(repo)).replace('\\','/'),'sha256':sha(p)}
    write(inventory,inv)
    statuspath=base/'status/windows.json';status=load(statuspath)
    journal=load(diag/'root-dh-primary-joint-after-initialization-2516-successor-3130/journal.json')
    status['snapshot_utc']=datetime.now(timezone.utc).isoformat()
    status['synchronized_origin_sha']=m['parent_commit']
    status['active_controller'].update({'settled_dh_phases':len(journal),'settled_dh_modules':sum(x.get('modules',0) for x in journal),
      'settled_dh_audits':sum(x.get('exports',0) for x in journal),
      'whole_root_complete':(diag/'root-field-native-epk-cast-repair-3130/complete.txt').exists()})
    status['checked_connected_subgroup_semantics_20261009_02']={'source_commit':source_commit,'receipt':str(p.relative_to(base)).replace('\\','/'),
      'sha256':sha(p),'unique_new_theorems':3,'global_order_explicit':True,'coverage02_coherent_replay':True,'full_transfer':'OPEN'}
    write(statuspath,status)
    print(json.dumps({'source_commit':source_commit,'receipt_sha256':sha(p),'fresh_modules':len(modules),'audits':total,'settled_dh_phases':len(journal)}))
else:raise ValueError(phase)
