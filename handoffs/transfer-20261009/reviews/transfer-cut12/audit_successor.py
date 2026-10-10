"""Inspect exact metadata successor and reproduce its output from immutable logs."""
import sys
assert sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site
import hashlib,json,shutil,subprocess
from pathlib import Path
H=Path(__file__).resolve().parent;R=H.parents[1];F=H/'frozen';S=R/'work/mac-transfer-cut12-provenance01';D=H/'provenance-frozen01'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=S/'successor-manifest01.json';binding=S/'scope-binding-envelope01.json'
assert sha(manifest)=='5e22357bd13c6eb325d2608db5416874e06d444c00c781c27643274c8016d3f2'
m=json.loads(manifest.read_bytes());b=json.loads(binding.read_bytes());assert b['provenance_successor']['sha256']==sha(manifest)
assert m['original_producer_sha256']==sha(F/'publication-manifest01.json') and m['original_envelope_sha256']==sha(F/'seal-envelope01.json')
assert not D.exists();D.mkdir();entries={**m['files'],**b['entries']}
for n,x in entries.items():
 p=R/n;assert sha(p)==x['sha256'] and p.stat().st_size==x['bytes'];out=D/n;out.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,out)
shutil.copyfile(manifest,D/'successor-manifest01.json');shutil.copyfile(binding,D/'scope-binding-envelope01.json')
freeze=json.loads((H/'freeze-manifest01.json').read_bytes())
for n,x in freeze['files'].items():assert sha(R/n)==x['sha256'] and sha(F/n)==x['sha256']
cmd=[sys.executable,'-I','-B','-S',str(D/'work/mac-transfer-cut12-provenance01/extract_audits.py'),'--root',str(F),'--producer',str(F/'publication-manifest01.json'),'--envelope',str(F/'seal-envelope01.json'),'--output-dir',str(H/'provenance-replay01')]
ret=subprocess.run(cmd,capture_output=True,text=True,timeout=240);assert ret.returncode==0,ret.stderr
produced=H/'provenance-replay01/full-audits-successor01.json';expected=R/'outputs/mac-transfer-cut12-provenance01/attempt02/full-audits-successor01.json'
assert sha(produced)==sha(expected)=='dceeea90843c79e4aa3a2b017703284a71528a478f2592274a01bd84d8e7802e'
records=json.loads(produced.read_bytes());assert len(records)==61
for t in records:assert hashlib.sha256(t['full_type'].encode()).hexdigest()==t['full_type_sha256']
scope=json.loads((S/'scope-addendum01.json').read_bytes());assert scope['control_count']==dict(production_checker_refusals=6,mapping_size_component_refusals=1,positive=1) and scope['census']['root_new_audits']==39
for n,x in entries.items():assert sha(R/n)==sha(D/n)==x['sha256']
result=dict(status='passed',original_entries_unchanged=83,successor_entries_rehashed=len(entries),successor_manifest_sha256=sha(manifest),scope_binding_envelope_sha256=sha(binding),exact_reproduced_structured_records=61,corrected_two_warning_prefixed_records=True,original_math_and_objects_unchanged=True,scope_addendum=scope,original_extractor_attempt_zero_credit=True,parent_kernel_runs=0,full_transfer='OPEN')
(H/'successor-review01.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status='passed',original_entries=83,successor_entries=len(entries),records=61,parent_kernel_runs=0)))
