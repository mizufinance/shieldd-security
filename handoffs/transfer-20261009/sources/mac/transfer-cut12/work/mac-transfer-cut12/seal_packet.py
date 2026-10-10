"""Seal exact generated/proof/import identities; no Lean execution or publication."""
import hashlib,json,re,runpy,sys
from pathlib import Path
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-transfer-cut12';P=S/'project'
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  while chunk:=f.read(1024**2):h.update(chunk)
 return h.hexdigest()
validate=runpy.run_path(str(S/'audit_log.py'))['validate']
current=[('TransferCut12ProbeData01',1),('TransferCut12ProductProbe01',1),('TransferCut12Data01',2),('TransferCut12Proof01',1),('TransferCut12Joined01',2),('TransferCut12Checked01',1),('TransferCut12Controls01',2)]
fresh=[];failed=[];all_audits=[];custom={};official={};selected={}
def include(path,kind,publication=True):
 assert path.is_file() and not path.is_symlink(),path
 selected[str(path.relative_to(R))]=dict(sha256=sha(path),bytes=path.stat().st_size,kind=kind,publication=publication)
for name,index in current:
 source=P/'ShielddSecurity'/f'{name}.lean';obj=P/'.lake/build/lib/lean/ShielddSecurity'/f'{name}.olean'
 rp=O/f'build-{name}-{index:02d}.json';lp=rp.with_suffix('.log');r=json.loads(rp.read_text())
 assert r['status']=='passed' and sha(source)==r['source_sha256'] and sha(obj)==r['object_sha256'] and sha(lp)==r['log_sha256']
 audit=validate(lp.read_text(),r['expected_axiom_names'],r['expected_signature_names'])
 assert audit['axiom_audits']==r['axiom_audits'] and audit['full_signature_sha256']==r['full_signature_sha256']
 assert r['command'][4:6]==['-j1','-M2048'] and r['lean_heap_limit_MiB']==2048 and r['timeout_seconds']==240
 assert r['process_group_rss_limit_bytes']==4*1024**3 and r['minimum_memory_free_percent']>=15 and r['minimum_disk_free_bytes']>=2*1024**3
 assert re.search(r'^set_option maxHeartbeats 900000$',source.read_text(),re.M)
 for filename,digest in r['guard_sources_sha256'].items():assert sha(S/filename)==digest
 cursor=0;text=lp.read_text()
 for declared in r['expected_signature_names']:
  m=re.search(r"'"+re.escape(declared)+r"' (depends on axioms: \[[^\]]*\]|does not depend on any axioms)",text[cursor:]);assert m
  begin=cursor+m.start();end=cursor+m.end()
  all_audits.append(dict(name=declared,full_type=text[cursor:begin].strip(),axioms=m.group(1),full_type_sha256=r['full_signature_sha256'][declared],raw_log=str(lp.relative_to(R)),raw_log_sha256=sha(lp)))
  cursor=end
 fresh.append(dict(module=name,receipt_path=str(rp.relative_to(R)),receipt_sha256=sha(rp),source_sha256=sha(source),object_sha256=sha(obj),source_bytes=source.stat().st_size,object_bytes=obj.stat().st_size,seconds=r['seconds'],peak_group_rss_bytes=r['peak_group_rss_bytes'],audits=r['axiom_audits'],classification='fresh named execution'))
 include(source,'generated Lean');include(rp,'fresh accepted receipt');include(lp,'raw build observation LOCAL ONLY',False)
 for mod,identity in r['frozen_imports'].items():
  if mod.startswith('ShielddSecurity.'):
   sp=P/(mod.replace('.','/')+'.lean');op=P/'.lake/build/lib/lean'/(mod.replace('.','/')+'.olean')
   assert sha(sp)==identity['source_sha256'] and sha(op)==identity['object_sha256'];custom[mod]=dict(**identity,source_path=str(sp.relative_to(R)),object_path=str(op.relative_to(R)))
  elif mod=='package':
   assert sha(P/'lakefile.lean')==identity['lakefile_sha256'] and sha(P/'lake-manifest.json')==identity['lake_manifest_sha256'] and sha(P/'lean-toolchain')==identity['toolchain_sha256']
  elif mod=='official_import_closure':
   mp=O/identity['manifest_file'];assert sha(mp)==identity['manifest_sha256'];official[mp]=json.loads(mp.read_text());include(mp,'immutable official import manifest')
for mp,data in official.items():
 for relative,digest in data['files'].items():
  label,rest=relative.split('/',1)
  base=Path.home()/'.elan/toolchains/leanprover--lean4---v4.30.0' if label=='lean4' else P/'.lake/packages'/label
  assert sha(base/rest)==digest,'official object/source changed: '+relative
inherit=json.loads((O/'inherited-qualification01.json').read_text())
for name,identity in inherit['reused'].items():
 source=P/'ShielddSecurity'/f'{name}.lean';obj=P/'.lake/build/lib/lean/ShielddSecurity'/f'{name}.olean'
 assert sha(source)==identity['source_sha256'] and sha(obj)==identity['object_sha256']
 assert sha(R/identity['original_receipt_path'])==identity['original_receipt_sha256']
for name,index in [('TransferCut12Data01',1),('TransferCut12Joined01',1),('TransferCut12Controls01',1)]:
 rp=O/f'build-{name}-{index:02d}.json';r=json.loads(rp.read_text());assert r['status']=='failed'
 historical=S/'source-history'/r['source_sha256']/f'{name}.lean';assert sha(historical)==r['source_sha256']
 include(historical,'failed source ZERO CREDIT');include(rp,'failed receipt ZERO CREDIT');include(rp.with_suffix('.log'),'raw failed observation LOCAL ONLY',False)
 failed.append(dict(module=name,attempt=index,reason=r.get('failure_observation'),receipt_path=str(rp.relative_to(R)),source_sha256=r['source_sha256'],classification='failed elaboration ZERO CREDIT'))
for filename in ['generate_probe.py','generate_cut.py','generate_join.py','generate_checked.py','supported_verify_replay.py','make_portable.py','test_portable.py','qualify_cut.py','run_qualification.py','build_bounded.py','freeze_external.py','audit_log.py','seal_packet.py','run_seal.py']:
 include(S/filename,'maintained generator or verification guard')
for path in (S/'portable01').rglob('*'):
 if path.is_file():include(path,'closed portable input or maintained recipe')
for path in sorted(O.glob('*.json')):
 if path.name.startswith('build-') or path.name.startswith('official-') or path.name.endswith('-build-179'+'.json'):continue
 if re.search(r'-build-\d+\.json$',path.name):continue
 include(path,'compact receipt / data qualification / exact provenance')
for path in [P/'lakefile.lean',P/'lake-manifest.json',P/'lean-toolchain']:
 include(path,'exact package source')
summary=dict(status='sealed_pending_parent_review',scope='Cut-first867steps1157selectedrows; both explicit source formulas, SAME finalrho hash6domain17nineinputs thenhash3domain18, all22735originalinputs/copy/union-gap frames.',
 fresh_modules=7,successor_modules=5,full_type_axiom_pairs=sum(x['audits'] for x in fresh),fresh=fresh,failed=failed,inherited_unexecuted=len(inherit['reused']),current_owned_imports=custom,
 generated_sources=7,kernel_control_scope='1positive+6productioncutcheckerrefusals+1reversecoveragecomponentrefusal; no semantic inequality claim, no wholejoinedcandidatechecker',
 portable_data_controls=7,portable_replay='7byte-identical sources; zero Lean',
 counts=dict(cut_materialized_product_steps=2,cut_fresh_columns=4,cut_with_copy_steps=3,cut_rows=5,joined_steps=867,joined_rows=1157,single_copy_capture_index=200769),
 import_floor='No fresh cost module; prior upstream11 floor totalRSS1958739968B, not a marginal subtraction.',
 total_seconds=sum(x['seconds'] for x in fresh),total_source_bytes=sum(x['source_bytes'] for x in fresh),total_object_bytes=sum(x['object_bytes'] for x in fresh),max_RSS_bytes=max(x['peak_group_rss_bytes'] for x in fresh),
 open=['larger parent page/full200770formalrowAt','native/rawconsumer/callsite identity','later consumer preservation','whole joined candidate checker','fullTransfer'],heavy_processes_remaining=False,
 publication_ack='7ea375d0f6e6f9eb5b3ddcb24341e60fcd734cef')
for name,value in [('final-summary01.json',summary),('full-audits01.json',all_audits)]:
 p=O/name;assert not p.exists();p.write_text(json.dumps(value,indent=2)+'\n');include(p,'final compact summary or complete type/axiom census')
manifest=O/'publication-manifest01.json';assert not manifest.exists()
manifest.write_text(json.dumps(dict(schema='cut12-producer-seal-v1',files=selected,math_acceptance='pending parent actual Opus5.5 review; no global certification'),indent=2)+'\n')
print(json.dumps(dict(status='sealed',producer_sha256=sha(manifest),entries=len(selected),publication_entries=sum(x['publication'] for x in selected.values()),fresh=7,audits=summary['full_type_axiom_pairs'])),flush=True)
