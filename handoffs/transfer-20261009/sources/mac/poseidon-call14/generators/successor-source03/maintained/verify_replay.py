"""Closed explicit-path isolated56-source replay; validate2accepted inputs, ZERO Lean."""
import argparse,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site
S=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();p=argparse.ArgumentParser()
for n in ['inventory','source-inventory','input','parameters','topology','imports','probe-source-dir','output-dir']:p.add_argument('--'+n,type=Path,required=True)
for n in ['inventory-sha256','source-inventory-sha256']:p.add_argument('--'+n,required=True)
a=p.parse_args();assert sha(a.inventory)==a.inventory_sha256 and sha(a.source_inventory)==a.source_inventory_sha256;i=json.loads(a.inventory.read_text());si=json.loads(a.source_inventory.read_text())
def closed():
 assert {p.name for p in S.iterdir()}==set(i['maintained_files'])
 for n,e in i['maintained_files'].items():p=S/n;assert p.is_file() and not p.is_symlink() and sha(p)==e['sha256'] and p.stat().st_size==e['bytes']
 assert sha(Path(__file__))==i['maintained_files'][Path(__file__).name]['sha256']
closed();assert sha(a.input)==si['input_sha256'] and sha(a.parameters)==si['parameters_sha256'] and sha(a.imports)==si['probe_imports_sha256']
assert not a.output_dir.exists();a.output_dir.mkdir(parents=True)
command=[sys.executable,'-I','-B','-S',str(S/'generate_successors.py')]
for n,v in [('inventory',a.inventory),('inventory-sha256',a.inventory_sha256),('input',a.input),('parameters',a.parameters),('topology',a.topology),('imports',a.imports),('probe-source-dir',a.probe_source_dir),('output-dir',a.output_dir/'sources'),('metadata-dir',a.output_dir/'metadata')]:command.extend(['--'+n,str(v)])
closed();proc=subprocess.run(command,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60);(a.output_dir/'generator.stdout.txt').write_text(proc.stdout);(a.output_dir/'generator.stderr.txt').write_text(proc.stderr);closed();assert proc.returncode==0,'generator refused; logs retained'
assert {p.name for p in (a.output_dir/'sources').iterdir()}=={n+'.lean' for n in si['successor_topological_order']}
for n in si['full_topological_order']:
 p=(a.probe_source_dir if n in si['accepted_probes'] else a.output_dir/'sources')/(n+'.lean');e=si['modules'][n];assert p.is_file() and not p.is_symlink() and sha(p)==e['sha256'] and p.stat().st_size==e['bytes']
closed();result={'status':'passed','new_unbuilt_sources':56,'accepted_probe_input_sources':2,'ALLsource_identities':58,'new_source_bytes':sum(si['modules'][n]['bytes'] for n in si['successor_topological_order']),'kernel_runs':0,'fresh_proof_credit':0,'command':command,'inventory_sha256':sha(a.inventory),'source_inventory_sha256':sha(a.source_inventory),'executing_recipe_sha256':sha(Path(__file__)),'Python_version':sys.version,'scope':'DATA-only56byte-generation and2accepted-input identitycheck; no proof replay; all56remainUNBUILT'}
(a.output_dir/'replay-result01.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
