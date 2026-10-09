from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, sys

repo=Path('C:/src/shieldd-transfer-windows-publication-20261009')
local=Path('C:/src/shieldd-transfer-handoffs')
diag=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
base=repo/'handoffs/transfer-20261009'
dest=base/'sources/windows/concrete-field-20261009-01'
canonical=repo/'circuits/ShielddSecurity'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def write(p,v):
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_bytes((json.dumps(v,indent=2)+'\n').encode())
def git(*args):return subprocess.check_output(['git','-C',str(repo),*args],text=True).strip()
runs={
 'pilot05':('windows-field-certificate-pilot-20261009-05','safe-field-certificate-pilot-boundary-2026100905',4,15),
 'tree03':('windows-field-certificate-tree-20261009-03','safe-field-certificate-tree-boundary-2026100903',38,76),
 'concrete01':('windows-field-concrete-20261009-01','safe-field-concrete-boundary-2026100901',2,15)}
for stem,boundary,_,_ in runs.values():
    for d in [diag/(stem+'-kernel'),diag/boundary]:
        assert (d/'complete.txt').exists() and (d/'end.txt').exists()
        assert (d/'exit.txt').read_text().strip()=='0'
    assert (diag/boundary/'resume-status.txt').read_text().strip()=='0'
handwritten=['ModularPower','LucasCertificate','FieldCertificateSmallPilot01','ConcreteJubjubField01']
phase=sys.argv[1]
if phase=='sources':
    assert not dest.exists();dest.mkdir(parents=True)
    files={}
    def copy(p,rel):
        target=dest/rel;target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(p.read_bytes());files[rel]={'sha256':sha(target),'bytes':target.stat().st_size}
    for name in handwritten:copy(canonical/(name+'.lean'),'handwritten/'+name+'.lean')
    generated=local/'field-certificate-tree-20261009-01'
    gm=load(generated/'manifest.json')
    for name,item in gm['files'].items():
        p=generated/'ShielddSecurity'/(name+'.lean');assert sha(p)==item['sha256']
        target=canonical/p.name;assert not target.exists();target.write_bytes(p.read_bytes())
    copy(generated/'manifest.json','generated-manifest.json')
    for p in [local/'generate-field-certificate-tree-20261009-01.py',Path(__file__),
        local/'inspect-field-external-closure-20261009-01.py',local/'inspect-field-concrete-closure-20261009-01.py',
        local/'make-field-concrete-inspection-20261009-01.py',local/'make-field-concrete-preparer-20261009-01.py',
        local/'compose-field-cache-20261009-03.py',local/'compose-field-cache-20261009-07.py']:
        copy(p,'recipes/'+p.name)
    for stem,_,_,_ in runs.values():
        copy(diag/(stem+'-source/manifest.json'),'inputs/'+stem+'.json')
        for p in [local/('prepare-'+stem+'.py'),local/('run-safe-'+stem+'.ps1'),
                  diag/('root-'+stem+'.ps1'),diag/('audit-'+stem+'.py')]:copy(p,'recipes/'+p.name)
    upstream=Path('C:/src/shieldd-formal/circuits/.lake/packages/mathlib/Mathlib/NumberTheory/LucasPrimality.lean')
    copy(upstream,'upstream/Mathlib/NumberTheory/LucasPrimality.lean')
    for label in ['01','02','03','04']:
        stem='windows-field-certificate-pilot-20261009-'+label
        for p in [local/('prepare-'+stem+'.py'),local/('run-safe-'+stem+'.ps1'),diag/('root-'+stem+'.ps1'),diag/('audit-'+stem+'.py')]:
            if p.exists():copy(p,'failed/pilot'+label+'/'+p.name)
        stage=diag/(stem+'-source')
        if stage.exists():
            for p in stage.glob('*.lean'):copy(p,'failed/pilot'+label+'/'+p.name)
            copy(stage/'manifest.json','failed/pilot'+label+'/manifest.json')
    for label in ['01','02']:
        stem='windows-field-certificate-tree-20261009-'+label
        for p in [local/('prepare-'+stem+'.py'),local/('run-safe-'+stem+'.ps1'),diag/('root-'+stem+'.ps1'),diag/('audit-'+stem+'.py')]:
            if p.exists():copy(p,'failed/tree'+label+'/'+p.name)
        stage=diag/(stem+'-source')
        if (stage/'manifest.json').exists():copy(stage/'manifest.json','failed/tree'+label+'/manifest.json')
    for label in ['01','03']:
        p=local/('compose-field-cache-20261009-'+label+'.py')
        if p.exists() and 'recipes/'+p.name not in files:copy(p,'recipes/'+p.name)
    resolution={}
    for stem,_,_,_ in runs.values():
        m=load(diag/(stem+'-kernel/manifest.json'))
        identities={name:item['sha256'] for name,item in m['sources'].items()}
        identities.update({x['name']:x['original_source_sha256'] for x in m.get('reused',[])})
        for name,digest in identities.items():
            candidates=[canonical/(name+'.lean'),dest/'upstream/Mathlib/NumberTheory/LucasPrimality.lean'] if name=='UpstreamLucasPrimality' else [canonical/(name+'.lean')]
            if not any(p.exists() and sha(p)==digest for p in candidates):
                candidates=list((base/'sources').rglob(name+'.lean'))
            matches=[p for p in candidates if p.exists() and sha(p)==digest];assert matches,(name,digest)
            resolution[name]={'path':matches[0].relative_to(repo).as_posix(),'sha256':digest}
    write(dest/'dependency-resolution.json',resolution)
    files['dependency-resolution.json']={'sha256':sha(dest/'dependency-resolution.json'),'bytes':(dest/'dependency-resolution.json').stat().st_size}
    write(dest/'manifest.json',{'files':files,'canonical_generated':{n:i['sha256'] for n,i in gm['files'].items()},
       'parent_commit':git('rev-parse','HEAD'),'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a',
       'candidate_sha256':gm['candidate_sha256'],'mathlib_commit':'c5ea00351c28e24afc9f0f84379aa41082b1188f',
       'scope':'Mathematical prime field, canonical mathematical codec, exact coefficient and imaginary witness, nonsquare coefficient',
       'native_codec':'OPEN','standard_curve_model':'OPEN','curve_order':'OPEN','full_transfer':'OPEN'})
    print(json.dumps({'files':len(files),'closure':len(resolution),'manifest_sha256':sha(dest/'manifest.json')}))
elif phase=='refresh-publisher':
    p=dest/'recipes'/Path(__file__).name;p.write_bytes(Path(__file__).read_bytes())
    m=load(dest/'manifest.json');m['files']['recipes/'+p.name]={'sha256':sha(p),'bytes':p.stat().st_size}
    write(dest/'manifest.json',m)
elif phase=='verify-index':
    manifest=load(dest/'manifest.json')
    for rel,item in manifest['files'].items():
        path=(dest/rel).relative_to(repo).as_posix()
        assert hashlib.sha256(subprocess.check_output(['git','-C',str(repo),'show',':'+path])).hexdigest()==item['sha256'],path
    for name,digest in manifest['canonical_generated'].items():
        assert hashlib.sha256(subprocess.check_output(['git','-C',str(repo),'show',':circuits/ShielddSecurity/'+name+'.lean'])).hexdigest()==digest
    for name in handwritten:
        assert hashlib.sha256(subprocess.check_output(['git','-C',str(repo),'show',':circuits/ShielddSecurity/'+name+'.lean'])).hexdigest()==sha(canonical/(name+'.lean'))
    print('Exact source Git index bytes PASS')
elif phase=='receipts':
    result={}
    for label,(stem,boundary,module_count,audit_count) in runs.items():
        kernel=diag/(stem+'-kernel');m=load(kernel/'manifest.json');modules={}
        for name in m['order']:
            leaf=kernel/name;a=load(leaf/'audit.json')
            assert (leaf/'end.txt').exists() and (leaf/'exit.txt').read_text().strip()=='0' and not (leaf/'stop.txt').exists()
            rel=m['sources'][name].get('lean_relative_path','ShielddSecurity/'+name+'.lean')
            assert sha(kernel/'project'/rel)==m['audited_candidates'][name]==a['candidate_sha256']
            assert a['full_types_checked']
            for axioms in a['axioms'].values():assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
            modules[name]={'audit':a,'actual_exit':0,'stdout_sha256':sha(leaf/'stdout.txt'),'stderr_sha256':sha(leaf/'stderr.txt')}
        assert len(modules)==module_count and sum(x['audit']['audits'] for x in modules.values())==audit_count
        result[label]={'fresh_modules':module_count,'audits':audit_count,'modules':modules,'qualified_reused_modules':m.get('reused',[]),
         'manifest_sha256':sha(kernel/'manifest.json'),'recipe':load(kernel/'recipe.json'),
         'root_resume_status':0,'actual_exit':0,'start':(kernel/'start.txt').read_text().strip(),'end':(kernel/'end.txt').read_text().strip()}
    failures={}
    reasons={'pilot01':'Missing nonexistent Mathlib.Tactic.Omega import',
       'pilot02':'Stage Mathlib prefix hid the existing external ZMod cache',
       'pilot03':'Whole cache exceeded fixed one GiB composer preflight bound before Lean',
       'pilot04':'Original 1118-module cache lacked ZMod.Basic closure',
       'tree01':'Preparation rejected incomplete foreign reuse; no heavy job launched',
       'tree02':'Foreign module private companion missing; import failed'}
    for label,reason in reasons.items():
        family='pilot' if label.startswith('pilot') else 'tree';n=label[-2:]
        stem='windows-field-certificate-'+family+'-20261009-'+n
        boundary=diag/('safe-field-certificate-'+family+'-boundary-20261009'+n)
        failures[label]={'reason':reason,'proof_and_control_credit':0,'lean_run':label not in ['tree01','pilot03']}
        if boundary.exists():
            resume=boundary/'resume-status.txt'
            if resume.exists():assert resume.read_text().strip()=='0';failures[label]['root_resume_status']=0
        for suffix in ['source/manifest.json','kernel/manifest.json','kernel/failure.txt']:
            p=diag/(stem+'-'+suffix)
            if p.exists():failures[label][suffix+'_sha256']=sha(p)
    inspection={}
    for key in ['field-external-closure-inspection-20261009-01','field-concrete-closure-inspection-20261009-01']:
        p=local/(key+'.json');v=load(p)
        inspection[key]={'sha256':sha(p),'source_modules':len(v['sources']),'artifact_files':len(v['files']),'bytes':v['bytes'],'missing':v['missing'],
         'identity_only_no_credit':True,'reproduce_with_published_inspector':True}
    receipt={'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','source_commit':git('rev-parse','HEAD'),
     'handwritten_commit':sys.argv[2],'parent_commit':'ab3b3a85d1a9d45677e834c488a175136659b80a',
     'source_packet_manifest_sha256':sha(dest/'manifest.json'),'source_index_exact_bytes_verified':True,
     'source_commit_diff_check_exit':int(sys.argv[3]),'source_diff_check_disposition':'Retained exact producer CRLF and blank EOF lines; no source bytes normalized',
     'generated_byte_reproduction':{'modules':38,'exact_bytes':True,'proof_credit':0},
     'fresh_module_checks':44,'theorem_audits':106,'unique_new_theorems':98,'replayed_theorem_audits':8,
     'runs':result,'failed_staging':failures,'external_closure':inspection,
     'negative_controls':{'actual_semantic_rejections':3,'module':'FieldCertificateSmallPilot01','cases':['bad factor','bad residue','bad base']},
     'mathematical_obligations':{'modulus_prime':'PROVED','imaginary_square_minus_one':'PROVED','coefficient_formula':'PROVED','coefficient_no_unit_square':'PROVED','canonical_codec':'CONSTRUCTED'},
     'native_codec':'OPEN','standard_curve_model':'OPEN','global_curve_order':'OPEN','full_transfer':'OPEN','native_successors':'UNRUN'}
    p=base/'receipts/windows/concrete-field-20261009-01.json';assert not p.exists();write(p,receipt)
    inventory=base/'reviews/windows-semantic-family-inventory-20261009-01.json';inv=load(inventory)
    inv['checked_concrete_field']={'receipt':p.relative_to(repo).as_posix(),'sha256':sha(p),'scope':receipt['mathematical_obligations'],
        'native_codec':'OPEN','standard_curve_model':'OPEN','global_curve_order':'OPEN'}
    for item in inv['owned_instance_obligations']:
        if 'nonsquare' in item.get('open',''):
            item['checked_concrete_field_receipt']=p.relative_to(repo).as_posix()
            item['open']='Concrete coefficient nonsquare and imaginary witness now proved over exact ZMod p. Full curve model and native refinements remain open.'
        if 'prime field' in item.get('obligation','').lower():
            item['checked_concrete_field_receipt']=p.relative_to(repo).as_posix()
            item['open']='Exact mathematical prime field, canonical decoder and BEWrite constructed. Native Scalar FFI encoder/reader agreement remains OPEN.'
    write(inventory,inv)
    statuspath=base/'status/windows.json';status=load(statuspath)
    journal=load(diag/'root-dh-primary-joint-after-initialization-2516-successor-3130/journal.json')
    status['snapshot_utc']=datetime.now(timezone.utc).isoformat();status['synchronized_origin_sha']=receipt['parent_commit']
    status['active_controller'].update({'settled_dh_phases':len(journal),'settled_dh_modules':sum(x.get('modules',0) for x in journal),
       'settled_dh_audits':sum(x.get('exports',0) for x in journal),'whole_root_complete':(diag/'root-field-native-epk-cast-repair-3130/complete.txt').exists()})
    status['checked_concrete_field_20261009_01']={'source_commit':receipt['source_commit'],'receipt':p.relative_to(base).as_posix(),'sha256':sha(p),
       'fresh_module_checks':44,'theorem_audits':106,'native_codec':'OPEN','standard_curve_model':'OPEN','curve_order':'OPEN','full_transfer':'OPEN'}
    write(statuspath,status)
    print(json.dumps({'receipt_sha256':sha(p),'fresh_module_checks':44,'audits':106,'settled_dh_phases':len(journal)}))
else:raise ValueError(phase)
