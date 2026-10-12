from pathlib import Path
import argparse,hashlib,json,os,re
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(65536),b''):h.update(b)
 return h.hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('--native-root',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();root=a.native_root.resolve();out=a.output.resolve();assert not out.exists()
inventory=json.loads((root/'source-inventory.json').read_bytes());build=json.loads((root/'map-build01/receipt.json').read_bytes());run=json.loads((root/'native-map-tests01/receipt.json').read_bytes())
assert build['status']=='build_passed' and run['status']=='two_native_map_controls_passed' and run['exit']==0 and run['stop'] is None
assert build['runtime_sha']==run['runtime_sha']==inventory['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
assert build['source_inventory_sha256']==run['source_inventory_sha256']==sha(root/'source-inventory.json')
for row in inventory['files']:
 p=root/'source'/row['path'];assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],row['path']
assert len(build['binaries'])==1 and build['binaries'][0]==run['binary'];binary=Path(run['binary']['path']);assert sha(binary)==run['binary']['sha256']
names=['map::tests::native_and_circuit_match_arkworks_elligator_including_zero_and_full_field','map::tests::quadratic_choice_and_domain_separated_generator_bindings_are_not_optional'];assert run['test_names']==names
text=(root/'native-map-tests01/stdout.txt').read_text();results=(root/'native-map-tests01/libtest-results.txt').read_text()
assert '2 passed; 0 failed; 0 ignored; 0 measured;' in text and 'running 2 tests' in text
for name in names:assert text.count('test '+name+' ... ok')==1 and results.count('ok '+name)==1
source=root/'source/crates/crypto/circuits/src/map/tests.rs';assert source.stat().st_size==4795 and sha(source)=='903fbdd65ecb5549ab0e4235866504f940691adea3a0fa41159c87335d2c8f81'
assert build['seconds']<=7200 and build['peak_group_rss_bytes']<=4*1024**3 and run['seconds']<=7200
for folder in ['map-build01','native-map-tests01']:
 for s in json.loads((root/folder/'samples.json').read_bytes()):
  assert s['free_memory_percent']>=15 and s['free_disk_bytes']>=2*1024**3 and s['rss_bytes']<=4*1024**3
tmp=out.with_name(out.name+'.pending');tmp.mkdir()
evidence=dict(status='two_native_map_controls_passed',runtime_sha=run['runtime_sha'],source_inventory_sha256=run['source_inventory_sha256'],source_paths=len(inventory['files']),map_test_source_sha256=sha(source),binary_sha256=run['binary']['sha256'],test_names=names,build_seconds=build['seconds'],build_peak_sampled_group_rss_bytes=build['peak_group_rss_bytes'],guarded_run_seconds=run['seconds'],libtest_seconds=float(re.search(r'finished in ([0-9.]+)s',text)[1]),run_peak_rss='Too short for reliable peak RSS; do not interpret the32KiB first sample as execution peak.',observations=run['observations'],scope='Finite SDK/Commonware/Arkworks map comparisons and wrong-output/inverted-choice/domain-separation controls on retained diagnostic source composition. Source identity is checked; full native trace refinement and Transfer certification are not proved.',source_composition='Exact clean844389ee archive plus recorded52-path diagnostic overlay; map test source unchanged from lock.',full_transfer='OPEN',certification=False,native_credit=2,stdout_sha256=sha(root/'native-map-tests01/stdout.txt'),results_sha256=sha(root/'native-map-tests01/libtest-results.txt'),build_receipt_sha256=sha(root/'map-build01/receipt.json'),run_receipt_sha256=sha(root/'native-map-tests01/receipt.json'),refresh_sha256=sha(Path(__file__)),resources=dict(threads=1,rss_bytes=4*1024**3,deadline_seconds=7200,free_memory_percent=15,free_disk_bytes=2*1024**3,macOS_sampling_only=True,linux_cgroup_and_task_swap_not_portable=True))
(tmp/'evidence.json').write_text(json.dumps(evidence,indent=2,sort_keys=True)+'\n');os.replace(tmp,out);print(json.dumps(dict(status=evidence['status'],native_credit=2)))

