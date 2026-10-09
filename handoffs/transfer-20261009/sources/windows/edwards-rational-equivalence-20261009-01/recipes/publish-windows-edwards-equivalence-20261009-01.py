from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, sys
repo=Path('C:/src/shieldd-transfer-windows-publication-20261009')
local=Path('C:/src/shieldd-transfer-handoffs');diag=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
base=repo/'handoffs/transfer-20261009';dest=base/'sources/windows/edwards-rational-equivalence-20261009-01'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def write(p,v):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((json.dumps(v,indent=2)+'\n').encode())
def git(*args):return subprocess.check_output(['git','-c','core.longpaths=true','-C',str(repo),*args],text=True).strip()
parent='4c0ddf35719d023b9e5ee1ab0331a0173d08d9fa'
runs=[('windows-edwards-algebra-20261009-02','safe-edwards-algebra-boundary-2026100902',10),
      ('windows-edwards-map-20261009-05','safe-edwards-map-boundary-2026100905',15),
      ('windows-edwards-equivalence-20261009-02','safe-edwards-equivalence-boundary-2026100902',24)]
for stem,boundary,count in runs:
    for p in [diag/(stem+'-kernel'),diag/boundary]:
        assert (p/'complete.txt').exists() and (p/'end.txt').exists()
        assert (p/'exit.txt').read_text().strip()=='0'
    assert (diag/boundary/'resume-status.txt').read_text().strip()=='0'
phase=sys.argv[1]
if phase=='sources':
    assert not dest.exists();dest.mkdir(parents=True);files={};resolution={}
    def copy(p,rel):
        target=dest/rel;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(p.read_bytes())
        files[rel]={'sha256':sha(target),'bytes':target.stat().st_size}
    for stem,boundary,count in runs:
        m=load(diag/(stem+'-kernel/manifest.json'))
        copy(diag/(stem+'-source/manifest.json'),'inputs/'+stem+'.json')
        for name,item in m['sources'].items():
            p=repo/'circuits/ShielddSecurity'/(name+'.lean');assert sha(p)==item['sha256']
            copy(p,'circuits/ShielddSecurity/'+p.name)
        for p in [local/('prepare-'+stem+'.py'),local/('run-safe-'+stem+'.ps1'),diag/('root-'+stem+'.ps1'),diag/('audit-'+stem+'.py')]:copy(p,'recipes/'+p.name)
        identities={name:v['sha256'] for name,v in m['sources'].items()}
        identities.update({v['name']:v['original_source_sha256'] for v in m['reused']})
        for name,digest in identities.items():
            candidates=[repo/'circuits/ShielddSecurity'/(name+'.lean')]
            if not any(p.exists() and sha(p)==digest for p in candidates):candidates=list((base/'sources/windows').rglob(name+'.lean'))
            matches=[p for p in candidates if p.exists() and sha(p)==digest];assert matches,(name,digest)
            resolution[name]={'path':matches[0].relative_to(repo).as_posix(),'sha256':digest}
    for p in [Path(__file__),local/'inspect-edwards-point-closure-20261009-01.py',local/'inspect-field-concrete-closure-20261009-01.py',
              local/'compose-edwards-algebra-cache-20261009-02.py',local/'compose-edwards-map-cache-20261009-05.py',local/'compose-edwards-equivalence-cache-20261009-02.py',
              local/'inspect-edwards-algebra-closure-20261009-02.py',local/'inspect-edwards-map-pilot-closure-20261009-05.py',local/'inspect-edwards-equivalence-closure-20261009-02.py']:
        copy(p,'recipes/'+p.name)
    failed=['windows-edwards-algebra-20261009-01']+['windows-edwards-map-20261009-'+n for n in ['01','02','03','04']]+['windows-edwards-equivalence-20261009-01']
    for stem in failed:
        stage=diag/(stem+'-source')
        for p in stage.glob('*.lean'):
            if '-audited' not in p.name:copy(p,'failed/'+stem+'/'+p.name)
        copy(stage/'manifest.json','failed/'+stem+'/manifest.json')
        for p in [local/('prepare-'+stem+'.py'),local/('run-safe-'+stem+'.ps1'),diag/('root-'+stem+'.ps1'),diag/('audit-'+stem+'.py')]:copy(p,'failed/'+stem+'/'+p.name)
    write(dest/'dependency-resolution.json',resolution)
    p=dest/'dependency-resolution.json';files[p.name]={'sha256':sha(p),'bytes':p.stat().st_size}
    write(dest/'manifest.json',{'files':files,'parent_commit':parent,'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a',
      'scope':'Conditional generic Edwards ↔ all Weierstrass affine equation solutions plus infinity; coordinate negation compatible',
      'fresh_modules':4,'declaration_audits':49,'new_theorems':41,'audited_definitions':8,
      'Mathlib_Point_join':'OPEN','concrete_parameters':'OPEN','discriminant':'OPEN','addition':'OPEN','StandardCurveModel':'OPEN','curve_order':'OPEN','native_representation':'OPEN','full_transfer':'OPEN'})
    print(json.dumps({'files':len(files),'closure':len(resolution),'manifest_sha256':sha(dest/'manifest.json')}))
elif phase=='verify-index':
    for rel,item in load(dest/'manifest.json')['files'].items():
        path=(dest/rel).relative_to(repo).as_posix()
        assert hashlib.sha256(subprocess.check_output(['git','-C',str(repo),'show',':'+path])).hexdigest()==item['sha256'],path
    for p in (dest/'circuits/ShielddSecurity').glob('*.lean'):
        assert hashlib.sha256(subprocess.check_output(['git','-C',str(repo),'show',':circuits/ShielddSecurity/'+p.name])).hexdigest()==sha(p)
    print('Exact source Git index bytes PASS')
elif phase=='receipts':
    outcomes={};names=set()
    for stem,boundary,count in runs:
        k=diag/(stem+'-kernel');m=load(k/'manifest.json');modules={}
        for name in m['order']:
            leaf=k/name;a=load(leaf/'audit.json');rel=m['sources'][name]['lean_relative_path']
            assert (leaf/'end.txt').exists() and (leaf/'exit.txt').read_text().strip()=='0' and not (leaf/'stop.txt').exists()
            assert a['full_types_checked'] and sha(k/'project'/rel)==m['audited_candidates'][name]==a['candidate_sha256']
            for n,axioms in a['axioms'].items():assert n not in names and set(axioms)<={'propext','Classical.choice','Quot.sound'};names.add(n)
            modules[name]={'audit':a,'actual_exit':0,'stdout_sha256':sha(leaf/'stdout.txt'),'stderr_sha256':sha(leaf/'stderr.txt')}
        assert sum(v['audit']['audits'] for v in modules.values())==count
        outcomes[stem]={'modules':modules,'manifest_sha256':sha(k/'manifest.json'),'recipe':load(k/'recipe.json'),'actual_exit':0,'root_resume_status':0,
            'start':(k/'start.txt').read_text().strip(),'end':(k/'end.txt').read_text().strip(),'qualified_reused_modules':m['reused'],
            'external_before_sha256':sha(k/'external-before.json'),'external_identity_rechecked':True}
    assert len(names)==49
    failures={}
    for family,labels in [('algebra',['01']),('map',['01','02','03','04']),('equivalence',['01'])]:
        for label in labels:
            stem='windows-edwards-'+family+'-20261009-'+label;k=diag/(stem+'-kernel');boundary=diag/('safe-edwards-'+family+'-boundary-20261009'+label)
            assert (boundary/'resume-status.txt').read_text().strip()=='0'
            failures[stem]={'proof_and_control_credit':0,'root_resume_status':0,'source_manifest_sha256':sha(diag/(stem+'-source/manifest.json')),
                'reason':{'algebra':'Unavailable tactic; replaced with ring identities',
                    'map':'Explicit symbolic denominator normalization/cancellation needed; no limit or hypothesis changes',
                    'equivalence':'Helper theorem needed explicit Parameters binder carrying characteristic-two exclusion'}[family]}
    inspect=load(local/'edwards-point-closure-inspection-20261009-01.json')
    receipt={'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','parent_commit':parent,'source_commit':git('rev-parse','HEAD'),
       'source_packet_manifest_sha256':sha(dest/'manifest.json'),'source_index_exact_bytes_verified':True,'source_diff_check_exit':int(sys.argv[2]),
       'source_diff_check_disposition':'Frozen producer bytes preserved including CRLF and EOF whitespace',
       'preparation_parent_label_disposition':'Inherited e90e824 field-preparer template labels identify historical inputs; actual synchronized campaign parent is 4c0ddf35, not an additional certification SHA',
       'runs':outcomes,'fresh_modules':4,'declaration_audits':49,'new_theorems':41,'audited_definitions':8,'failed_attempts':failures,'new_negative_control_credit':0,
       'Point_import_preflight':{'source_modules':len(inspect['sources']),'present_artifact_bytes':inspect['bytes'],'missing_artifacts':len(inspect['missing']),
         'limit_bytes':1024**3,'run':False,'proof_credit':0,'inspection_sha256':sha(local/'edwards-point-closure-inspection-20261009-01.json')},
       'explicit_parameters':['Field F','2 != 0','d != 0','NoUnitSquare d','imaginary * imaginary = -1','A * (1+d) = 2*(1-d)','B * (1+d) = -4'],
       'target':'Option {point:Group.Point F // Equation A B point.x point.y}',
       'exceptional_images':['Edwards (0,1) -> infinity','Edwards (0,-1) -> finite (0,0)'],
       'Mathlib_Point_join':'OPEN','concrete_parameters':'OPEN','discriminant':'OPEN','addition':'OPEN','StandardCurveModel':'OPEN','curve_order':'OPEN','native_representation':'OPEN','full_transfer':'OPEN'}
    p=base/'receipts/windows/edwards-rational-equivalence-20261009-01.json';assert not p.exists();write(p,receipt)
    inventory=base/'reviews/windows-semantic-family-inventory-20261009-01.json';inv=load(inventory)
    inv['checked_generic_rational_equivalence']={'receipt':p.relative_to(repo).as_posix(),'sha256':sha(p),
       'target':receipt['target'],'explicit_parameters':receipt['explicit_parameters'],
       'negation_compatible':True,'Mathlib_Point_join':'OPEN','concrete_parameters':'OPEN','StandardCurveModel':'OPEN','curve_order':'OPEN'}
    write(inventory,inv)
    statuspath=base/'status/windows.json';status=load(statuspath);journal=load(diag/'root-dh-primary-joint-after-initialization-2516-successor-3130/journal.json')
    status['snapshot_utc']=datetime.now(timezone.utc).isoformat();status['synchronized_origin_sha']=parent
    status['active_controller'].update({'settled_dh_phases':len(journal),'settled_dh_modules':sum(v.get('modules',0) for v in journal),
       'settled_dh_audits':sum(v.get('exports',0) for v in journal),'whole_root_complete':(diag/'root-field-native-epk-cast-repair-3130/complete.txt').exists()})
    status['edwards_rational_equivalence_20261009_01']={'source_commit':receipt['source_commit'],'receipt':p.relative_to(base).as_posix(),'sha256':sha(p),
       'declaration_audits':49,'Mathlib_Point_join':'OPEN','StandardCurveModel':'OPEN','curve_order':'OPEN','full_transfer':'OPEN'}
    write(statuspath,status)
    print(json.dumps({'receipt_sha256':sha(p),'audits':49,'settled_dh_phases':len(journal)}))
else:raise ValueError(phase)
