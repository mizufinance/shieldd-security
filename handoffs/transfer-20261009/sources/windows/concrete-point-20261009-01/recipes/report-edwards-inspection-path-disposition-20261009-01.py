from pathlib import Path
import hashlib,json
local=Path('C:/src/shieldd-transfer-handoffs');diag=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
shared=local/'edwards-map-pilot-closure-inspection-20261009-01.json'
history={}
for stem in ['windows-edwards-map-20261009-01','windows-edwards-equivalence-20261009-01','windows-edwards-equivalence-20261009-02']:
    p=diag/(stem+'-kernel/external-overlay.json');v=json.loads(p.read_text())
    history[stem]={'inspection_sha256':v['inspection_sha256'],'external_identities_sha256':v['identities_sha256'],
       'files':v['files'],'bytes':v['bytes'],'source_modules':v['source_modules'],
       'actual_batch_complete':(diag/(stem+'-kernel/complete.txt')).exists()}
current=hashlib.sha256(shared.read_bytes()).hexdigest()
assert current==history['windows-edwards-equivalence-20261009-02']['inspection_sha256']
assert len({v['external_identities_sha256'] for v in history.values()})==1
report={'kind':'Append-only inspection-path metadata disposition; no new proof credit',
 'shared_path':str(shared),'history':history,'current_sha256':current,
 'finding':'Template replacement omitted the inspection output suffix, so equivalence01 and02 reused the failed map01 inspection pathname.',
 'preserved':'Sealed Lean sources, audited candidates, guards, compiled outputs and recorded actual overlay identities were unchanged. Both earlier affected batches failed and have zero credit.',
 'actual_success':'equivalence02 used its matching current756-source inspection and the same independently hashed2984 external artifacts as the failed pilots; its49-declaration packet is not being replayed or promoted.',
 'future_fix':'New concrete and Point builders use explicit fresh inspection paths and reject an existing output; preserve original recipes and metadata.'}
out=local/'edwards-inspection-path-disposition-20261009-01.json';assert not out.exists();out.write_bytes((json.dumps(report,indent=2)+'\n').encode())
print(json.dumps({'report_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'new_proof_credit':0}))
