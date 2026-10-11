"""Parent source, generator, dependency and guard checks; no Lean execution."""
import hashlib
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

J = Path(__file__).resolve().parent
P = J/'packet01'
OLD = J.parent/'windows-sdk-admission-review01'
PRED = J.parent/'windows-capability-rows-review01'
CODEC = J.parent/'windows-sdk-codec-review01'
registry = Path('/Users/antoinecyr/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
def sha(b): return hashlib.sha256(b).hexdigest()
def save(name,data): (J/name).write_text(json.dumps(data,indent=2)+'\n')
M = json.loads((P/'manifest.json').read_bytes())
audits = {x['module']:x for x in json.loads((J/'audit-result01.json').read_bytes())['modules']}
old_audits = {x['module']:x for x in json.loads((OLD/'audit-result01.json').read_bytes())['modules']}
inherited = {x['module']:x for x in json.loads((PRED/'import-review01.json').read_bytes())['associations']}
codec_audits = {x['module']:x for x in json.loads((CODEC/'audit-result01.json').read_bytes())['modules']}
pred_audits = {x['module']:x for x in json.loads((PRED/'audit-result01.json').read_bytes())['modules']}
all_audits = {**old_audits, **codec_audits, **pred_audits, **audits}

inventory=[]
for spec in M['modules']:
    path=P/(spec['source_class']+'-source/ShielddSecurity')/(spec['module']+'.lean')
    text=path.read_text()
    stripped=re.sub(r'/-.*?-/', '', text, flags=re.S)
    stripped=re.sub(r'--[^\n]*','',stripped)
    assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|axiom|unsafe)\b',stripped)
    namespace=re.findall(r'(?m)^namespace ([\w.]+)\s*$',stripped)
    assert namespace==['ShielddSecurity.'+spec['module']]
    names=[]
    for match in re.finditer(r'(?m)^(?P<mods>(?:(?:noncomputable|private|protected)\s+)*)(?:def|abbrev|theorem|lemma|structure|inductive|class)\s+(?P<name>[\w.]+)',stripped):
        if 'private' not in match['mods'].split(): names.append(namespace[0]+'.'+match['name'])
    reported=[x['declaration'] for x in audits[spec['module']]['audits']]
    missing=sorted(set(names)-set(reported));extra=sorted(set(reported)-set(names))
    assert not extra
    assert not missing
    inventory.append({'module':spec['module'],'explicit_public_declarations':names,'reported_declarations':reported,'unaudited_public_definitions':missing,'report_order_differs':names!=reported})
assert sum(len(x['reported_declarations']) for x in inventory)==35

save('declaration-inventory01.json',{'explicit_public_inventory':inventory,'reported_declarations':35,'explicit_public_declarations':35,'pending_supplement':[],'kernel_replay':False})

source_snapshots=[]
runtime_snapshots=[]
runtime_root=J.parent.parent/'runtime-snapshot'
for path in sorted((P/'source-provenance/runtime').rglob('*')):
    if path.is_file():
        local=runtime_root/path.relative_to(P/'source-provenance/runtime')
        assert local.read_bytes()==path.read_bytes()
        runtime_snapshots.append({'path':str(path.relative_to(P)),'bytes':path.stat().st_size,'sha256':sha(path.read_bytes())})
save('runtime-source-review01.json',{'snapshot_files_exact':runtime_snapshots,'runtime_sha':M['runtime_sha'],'kind':'Exact clean runtime source comparison only; no native test or universal Rust refinement'})
for path in sorted((P/'source-provenance/pinned-sdk').rglob('*.rs')):
    local=registry/path.relative_to(P/'source-provenance/pinned-sdk')
    assert local.read_bytes()==path.read_bytes()
    source_snapshots.append({'path':str(path.relative_to(P)),'bytes':path.stat().st_size,'sha256':sha(path.read_bytes())})
save('sdk-source-review01.json',{'snapshot_files_exact':source_snapshots,'kind':'Exact previously archive-verified locked crate source comparison; source evidence, not native refinement'})

seen={};pools=[];categories={}
for path in sorted((P/'owned-import-context').rglob('composition-review.json')):
    pool=json.loads(path.read_bytes());selected=pool['selected']
    assert len(selected)==pool['objects'] and pool['admission_ready']
    assert len({x['module'] for x in selected})==len(selected)
    charged=sum(x['copy']['bytes'] for x in selected)
    assert charged==pool['charged_new_object_bytes']<=pool['artifact_cap_bytes']
    for x in selected:
        name=x['module'];source=x['source'];obj=x['object'];copy=x['copy']
        assert (copy['sha256'],copy['bytes'])==(obj['sha256'],obj['bytes'])
        if name in inherited and name not in audits:
            prior=inherited[name]
            assert (source['sha256'],source['bytes'],obj['sha256'],obj['bytes'])==tuple(prior['signature'])
            category='previously_reviewed_inherited_association'
        else:
            assert name in all_audits
            prior=all_audits[name]
            assert source['sha256']==prior['source_sha256']
            objects=[v for v in prior['receipt']['objects'] if v['path'].endswith('/'+name+'.olean') or v['path'].endswith('\\'+name+'.olean')]
            assert len(objects)==1 and (obj['sha256'],obj['bytes'])==(objects[0]['sha256'],objects[0]['bytes'])
            assert x['receipt']==prior['receipt']
            category='exact_qualified_predecessor_source_and_object'
        signature=(source['sha256'],source['bytes'],obj['sha256'],obj['bytes'])
        assert name not in seen or seen[name]['signature']==signature
        seen[name]={'signature':signature,'category':category}
    pools.append({'pool':str(path.relative_to(P)),'modules':len(selected),'charged_bytes':charged})
for x in seen.values():categories[x['category']]=categories.get(x['category'],0)+1
save('import-review01.json',{'kind':'Exact inherited/fresh source and copied-object receipt associations; no remote raw object replay',
    'unique_modules':len(seen),'categories':categories,'pools':pools,
    'associations':[dict(module=k,**v) for k,v in sorted(seen.items())],'full_transfer':'OPEN'})

baseline=(OLD/'packet01/execution-context/transfer-sdk-spend-auth-join-20261010-02/execute_bounded.py').read_bytes()
tasks=[]
for path in sorted((P/'execution-context').glob('*/execute_bounded.py')):
    assert path.read_bytes()==baseline
    plan=json.loads((path.parent/'plan.json').read_bytes())
    assert plan['limits']['heap_mib']==1536 and plan['limits']['threads']==1
    assert plan['limits']['max_heartbeats']==300000 and plan['limits']['max_rec_depth']==4096
    assert plan['limits']['all_bytes']==128*1024*1024
    tasks.append({'task':path.parent.name,'runner_byte_identical_to_accepted':True,'runner_sha256':sha(baseline)})
save('runner-review01.json',{'kind':'Both exact runner bodies byte-identical to accepted concrete cofactor runner, including memory/process/time/pressure/audit guards',
    'tasks':tasks,'packaging_inherited':{'object_bytes':8*1024*1024,'artifact_bytes':128*1024*1024}})
print(json.dumps({'declarations':35,'generated_sources':0,'locked_source_snapshots':len(source_snapshots),
                  'unique_imports':len(seen),'categories':categories,'runner_bodies':len(tasks)}))
