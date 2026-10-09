"""Append the completed seal guard without modifying the producer manifest."""
import hashlib,json
from pathlib import Path
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-subgroup-prime06'
def item(p,category,publish=True):
 return dict(path=str(p.relative_to(R)),category=category,publication=publish,
             bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
manifest=O/'publication-manifest01.json'
assert hashlib.sha256(manifest.read_bytes()).hexdigest()=='7bd0cd7a72b95b01bd5b14bed5b6fbaacbd4fe617b0e8b367e609a5959892414'
m=json.loads(manifest.read_text())
for row in m['files']:
 p=R/row['path'];assert p.stat().st_size==row['bytes'] and hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
guard=O/'seal-guard02.json';g=json.loads(guard.read_text());assert g['status']=='passed' and g['exit']==0
assert g['source_guards_after_equal'] and g['log_sha256']==hashlib.sha256(guard.with_suffix('.log').read_bytes()).hexdigest()
scope=O/'subgroup-prime-result01.json';v=json.loads(scope.read_text())
assert v['status']=='passed' and v['fresh_modules']==60 and v['fresh_audits']==133 and v['fresh_full_type_audits']==122
extra=[item(manifest,'unchanged_producer_manifest'),item(guard,'completed_seal_guard'),
       item(guard.with_suffix('.log'),'raw_completed_seal_observation_local_only',False),
       item(Path(__file__),'post_run_envelope_generator')]
value=dict(schema='finite-subgroup-prime-post-run-envelope-v1',producer_manifest=extra[0],
 producer_manifest_unchanged=True,additional_files=extra[1:],scope_reference=item(scope,'numeric_scope_and_measurements'),
 transport=dict(producer_files=len(m['files']),producer_publication_files=sum(x['publication'] for x in m['files']),
    append_publication_files=sum(x['publication'] for x in extra[1:]),raw_logs_and_oleans_local_only=True),
 fresh_executions=dict(passed_modules=60,axiom_audits=133,full_type_checks=122,Scalar_axiom_only_audits=11),
 inherited_proof_credit=m['inherited_imports'],full_transfer='OPEN')
dest=O/'publication-envelope01.json';assert not dest.exists();tmp=dest.with_suffix('.tmp');tmp.write_text(json.dumps(value,indent=2)+'\n');tmp.replace(dest)
print(json.dumps(dict(envelope_sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),manifest_sha256=extra[0]['sha256'],transport=value['transport'])))
