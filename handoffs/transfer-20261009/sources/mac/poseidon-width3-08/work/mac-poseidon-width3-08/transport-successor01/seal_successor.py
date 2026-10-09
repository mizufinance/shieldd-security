"""Seal append-only portable replay and transport classifications."""
import hashlib,json,os
from pathlib import Path
S=Path(__file__).resolve().parent;ROOT=S.parent.parents[1];OUT=ROOT/'outputs/mac-poseidon-width3-08'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
producer=OUT/'publication-manifest02.json';envelope=OUT/'publication-envelope01.json';m=json.loads(producer.read_text());e=json.loads(envelope.read_text());assert sha(producer)==e['producer_manifest_sha256']
for item in m['files']:assert sha(ROOT/item['path'])==item['sha256'],item['path']
result=ROOT/'work/width3-repro-portable01/replay-result.json';r=json.loads(result.read_text());guard=S/'portable-guard01.json';g=json.loads(guard.read_text());assert g['status']=='passed' and r['status']=='passed' and r['generated_sources']==78
assert sha(guard.with_suffix('.log'))==g['log_sha256'];assert sha(S/'verify_replay_portable.py')==g['source_sha256'];assert sha(producer)==r['producer_manifest_sha256']
result_copy=S/'portable-result01.json';assert not result_copy.exists();result_copy.write_bytes(result.read_bytes())
overrides=[dict(path='work/mac-poseidon-width3-08/port_full_generators.py',category='historical_source_only_bootstrap_not_supported_replay',publication=False),dict(path='outputs/mac-poseidon-width3-08/publication-manifest01.json',category='initial_refused_metadata_manifest_zero_publication_credit',publication=False)]
for i in [0,1,4]:overrides.append(dict(path=f'work/mac-poseidon-width3-08/project/ShielddSecurity/TransferPoseidonWidth3R{i:02d}08Proof01.lean',category='generated_instance',publication=True))
disposition=dict(schema='width3-portable-transport-disposition-v1',source_maintenance_choice='historical bootstrap alternative; actual9 maintained generators/templates are supported self-contained replay',bootstrap_hash='6ced33549fe38fc74cb8559ea02c01ebcb41af5d0c31d14997f9b1a23dce3b89',bootstrap_read_or_execution_required=False,classification_overrides=overrides,generated_sources=78,handwritten_helpers=2,verification_floor_modules=1,proof_modules=81,exact_fulltype_axiom_audits=1998,kernel_replays_for_maintenance=0,source_or_proof_credit_change=0,portable_recipe='verify_replay_portable.py with required --manifest --envelope --source-dir --small-descriptor --descriptor --parameter --output; verifies only shipped needed source inputs plus explicit qualified local descriptors/parameter',large_descriptors_publication=False,failed_replay_attempts='guard01 missing exporter identity file; guard02 header classification found75 rather than78; both preserved zero replay acceptance and zero kernel credit',failed_initial_manifest='active guard log included before closure; manifest01 refused. It was not accepted as an immutable packet; references may be stale. Manifest02/envelope01 fully rehashed and preserved unchanged.',full_transfer='OPEN')
p=S/'disposition01.json';assert not p.exists();p.write_text(json.dumps(disposition,indent=2)+'\n')
files=[]
for p in sorted(S.iterdir()):
 if not p.is_file():continue
 if p.name.startswith(('manifest','envelope')):continue
 historical=p.name.startswith('verify_replay-') or p.name in ['verify_replay.py','run_verify.py','replay-result01.json']
 files.append(dict(path=str(p.relative_to(ROOT)),sha256=sha(p),bytes=p.stat().st_size,category='historical_recipe_or_observation' if historical else 'portable_replay_or_disposition_or_proposal',publication=p.suffix!='.log' and not historical))
manifest=dict(schema='width3-append-only-transport-successor-v1',producer_manifest_path=str(producer.relative_to(ROOT)),producer_manifest_sha256=sha(producer),producer_envelope_path=str(envelope.relative_to(ROOT)),producer_envelope_sha256=sha(envelope),files=files,classification_overrides=overrides,prior_seal_unchanged=True,full_transfer='OPEN')
p=S/'manifest01.json';assert not p.exists();p.write_text(json.dumps(manifest,indent=2)+'\n')
q=S/'envelope01.json';assert not q.exists();q.write_text(json.dumps(dict(schema='width3-final-portable-envelope-v1',successor_manifest_path=str(p.relative_to(ROOT)),successor_manifest_sha256=sha(p),producer_manifest_path=str(producer.relative_to(ROOT)),producer_manifest_sha256=sha(producer),producer_envelope_path=str(envelope.relative_to(ROOT)),producer_envelope_sha256=sha(envelope),post_run_guard_path=str(guard.relative_to(ROOT)),post_run_guard_sha256=sha(guard),portable_result_sha256=sha(result_copy),proposal_path=str((S/'NEXT_TASK.md').relative_to(ROOT)),proposal_sha256=sha(S/'NEXT_TASK.md'),proof_credit_change=0,full_transfer='OPEN'),indent=2)+'\n')
for item in m['files']:assert sha(ROOT/item['path'])==item['sha256'],item['path']
print(json.dumps(dict(status='passed',successor_manifest_sha256=sha(p),successor_envelope_sha256=sha(q),producer_manifest_sha256=sha(producer),entries=len(files))))
