"""Reparse fresh successful existing logs; inherited receipts do not count."""
import hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];S=ROOT/'work/mac-poseidon-width6-upstream11';O=ROOT/'outputs/mac-poseidon-width6-upstream11'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
accepted=[];zero=[]
for p in sorted(O.glob('build-*.json')):
    raw=json.loads(p.read_text())
    if not any(str(S/'project') in x for x in raw.get('command',[]) if isinstance(x,str)):continue
    frozen=HERE/'frozen/project/ShielddSecurity'/(raw['module']+'.lean')
    if not frozen.exists():continue
    r=json.loads(p.read_text());name=r['module']
    if r['status']!='passed':zero.append({'receipt':p.name,'status':r['status'],'credit':0});continue
    source=S/'project/ShielddSecurity'/(name+'.lean');log=p.with_suffix('.log')
    assert sha(source)==sha(frozen)==r['source_sha256'] and sha(log)==r['log_sha256']
    assert r['exit']==0 and r['lean_heap_limit_MiB']==2048 and r['timeout_seconds']==240 and r['seconds']<=240
    assert r['process_group_rss_limit_bytes']==4*1024**3 and r['peak_group_rss_bytes']<=4*1024**3
    assert r['minimum_memory_free_percent']>=15 and r['minimum_disk_free_bytes']>=2*1024**3
    assert '-j1' in r['command'] and '-M2048' in r['command']
    assert r['frozen_imports']['mathlib_revision']=='c5ea00351c28e24afc9f0f84379aa41082b1188f'
    guards=[]
    for n,h in r['guard_sources_sha256'].items():
        current=S/n
        if sha(current)==h:bound=current
        else:
            candidates=[x for x in (O/'source-history').glob('*') if x.is_file() and sha(x)==h]
            assert len(candidates)==1,(p.name,n,h)
            bound=candidates[0]
        guards.append({'guard':n,'sha256':h,'exact_path':str(bound.relative_to(ROOT))})
    text=log.read_text();assert 'error:' not in text and 'sorryAx' not in text
    axioms=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text)
    axioms += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",text)]
    assert sorted(n for n,_ in axioms)==sorted(r['expected_axiom_names'])
    for n,v in axioms:assert {x.strip() for x in v.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'}
    for n,h in r['full_signature_sha256'].items():
        hits=re.findall(r'^@?'+re.escape(n)+r'\s*:[\s\S]*?(?=^\''+re.escape(n)+r'\')',text,re.M)
        assert len(hits)==1 and hashlib.sha256(hits[0].strip().encode()).hexdigest()==h
    assert len(axioms)==r['axiom_audits']==len(r['full_signature_sha256'])==len(r['expected_signature_names'])
    accepted.append({'module':name,'receipt_sha256':sha(p),'source_sha256':sha(source),'log_sha256':sha(log),'guard_source_identities':guards,'type_axiom_audits':len(axioms),'seconds':r['seconds'],'scope':'import cost True marker only' if 'ImportFloor' in name else 'named theorem/definition exact scope'})
i=1
while (HERE/f'receipt-audit{i:02d}.json').exists():i+=1
result={'schema':'parent-upstream11-current-source-existing-log-audit-v1','accepted':accepted,'modules':len(accepted),'type_axiom_audits':sum(x['type_axiom_audits'] for x in accepted),'failed_no_credit':zero,'inherited_receipts_not_fresh':True,'parent_kernel_runs':0,'whole_upstream_kernel_credit':0,'classification':'source-only snapshot/current exact receipt observation; final acceptance pending sealed packet and endpoint','full_transfer':'OPEN'}
(HERE/f'receipt-audit{i:02d}.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['accepted']}))
