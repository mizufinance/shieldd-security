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
OLD = J.parent/'windows-concrete-model-review01'
registry = Path('/Users/antoinecyr/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
def sha(b): return hashlib.sha256(b).hexdigest()
def save(name,data): (J/name).write_text(json.dumps(data,indent=2)+'\n')
M = json.loads((P/'manifest.json').read_bytes())
audits = {x['module']:x for x in json.loads((J/'audit-result01.json').read_bytes())['modules']}
old_audits = {x['module']:x for x in json.loads((OLD/'audit-result01.json').read_bytes())['modules']}
inherited = {x['module']:x for x in json.loads((OLD/'import-associations01.json').read_bytes())['associations']}
all_audits = dict(old_audits,**audits)

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
    assert names==reported
    inventory.append({'module':spec['module'],'explicit_public_declarations':names})
assert sum(len(x['explicit_public_declarations']) for x in inventory)==98

recipe=P/'recipes/portable-sdk-base-generator'
original=(P/'generation-context/qualified/generate.py').read_bytes()
portable=(recipe/'generate.py').read_bytes()
assert original.replace(b"ROOT.parent / 'transfer-sdk-spend-auth-proposal-20261010-01/proposals.json'",b"ROOT / 'inputs/proposals.json'")==portable
regen=J/'regeneration01'
regen.mkdir(exist_ok=False)
(regen/'inputs').mkdir()
shutil.copyfile(recipe/'generate.py',regen/'generate.py')
shutil.copyfile(recipe/'inputs/proposals.json',regen/'inputs/proposals.json')
run=subprocess.run([sys.executable,str(regen/'generate.py')],capture_output=True,timeout=20)
assert run.returncode==0 and not run.stderr
generated=(regen/'generated/SDKSpendAuthCertificates01.lean').read_bytes()
assert generated==(P/'generated-source/ShielddSecurity/SDKSpendAuthCertificates01.lean').read_bytes()
proposal=json.loads((recipe/'inputs/proposals.json').read_bytes())
constants=(registry/'reddsa-0.5.2/src/constants.rs').read_text()
match=re.search(r'pub const SPENDAUTHSIG_BASEPOINT_BYTES: \[u8; 32\] = \[(.*?)\];',constants,re.S)
sdk=list(map(int,re.findall(r'\d+',match.group(1))))
assert proposal['sdk_bytes']==sdk
p=52435875175126190479447740508185965837690552500527637822603658699938581184513
d=-10240*pow(10241,-1,p)%p
assert proposal['p']==p and proposal['d']==d
assert proposal['masked_y_bytes']==sdk[:31]+[sdk[31]&127]
x,y=proposal['sdk_point']
assert 0<=x<p and 0<=y<p and x%2==sdk[31]>>7
assert int.from_bytes(bytes(proposal['masked_y_bytes']),'little')==y
for x,y in proposal['double_chain']:
    assert (y*y-x*x-1-d*x*x*y*y)%p==0
for (x,y),(u,v) in zip(proposal['double_chain'],proposal['double_chain'][1:]):
    delta=d*x*x*y*y%p
    assert (1+delta)%p and (1-delta)%p
    assert u==2*x*y*pow((1+delta)%p,-1,p)%p
    assert v==(y*y+x*x)*pow((1-delta)%p,-1,p)%p
save('generator-review01.json',{'exact_generated_sha256':sha(generated),'bytes':len(generated),
    'unchanged_qualified_recipe_except_proposal_path':True,'explicit_public_inventory':inventory,
    'sdk_constant_matches_locked_crate':True,'independent_integer_doublings':3,'kernel_replay':False})

source_snapshots=[]
for path in sorted((P/'source-provenance/pinned-sdk').rglob('*.rs')):
    local=registry/path.relative_to(P/'source-provenance/pinned-sdk')
    assert local.read_bytes()==path.read_bytes()
    source_snapshots.append({'path':str(path.relative_to(P)),'bytes':path.stat().st_size,'sha256':sha(path.read_bytes())})
save('sdk-source-review01.json',{'snapshot_files_exact':source_snapshots,'kind':'Exact previously archive-verified locked crate source comparison; source evidence, not native refinement'})

seen={};pools=[];categories={}
for path in sorted((P/'owned-import-context').glob('*/composition-review.json')):
    pool=json.loads(path.read_bytes());selected=pool['selected']
    assert len(selected)==pool['objects'] and pool['admission_ready']
    assert len({x['module'] for x in selected})==len(selected)
    charged=sum(x['copy']['bytes'] for x in selected)
    assert charged==pool['charged_new_object_bytes']<=pool['artifact_cap_bytes']
    for x in selected:
        name=x['module'];source=x['source'];obj=x['object'];copy=x['copy']
        assert (copy['sha256'],copy['bytes'])==(obj['sha256'],obj['bytes'])
        if name in inherited:
            prior=inherited[name]
            assert source==prior['source'] and obj['sha256']==prior['object_sha256']
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

baseline=(OLD/'packet01/execution-context/transfer-concrete-cofactor-model-20261010-02/execute_bounded.py').read_bytes()
tasks=[]
for path in sorted((P/'execution-context').glob('*/execute_bounded.py')):
    assert path.read_bytes()==baseline
    plan=json.loads((path.parent/'plan.json').read_bytes())
    assert plan['limits']['heap_mib']==1536 and plan['limits']['threads']==1
    assert plan['limits']['max_heartbeats']==300000 and plan['limits']['max_rec_depth']==4096
    assert plan['limits']['all_bytes']==128*1024*1024
    tasks.append({'task':path.parent.name,'runner_byte_identical_to_accepted':True,'runner_sha256':sha(baseline)})
save('runner-review01.json',{'kind':'All seven exact runner bodies byte-identical to accepted concrete cofactor runner, including memory/process/time/pressure/audit guards',
    'tasks':tasks,'packaging_inherited':{'object_bytes':8*1024*1024,'artifact_bytes':128*1024*1024}})
print(json.dumps({'declarations':98,'generated_exact':True,'locked_source_snapshots':len(source_snapshots),
                  'unique_imports':len(seen),'categories':categories,'runner_bodies':len(tasks)}))
