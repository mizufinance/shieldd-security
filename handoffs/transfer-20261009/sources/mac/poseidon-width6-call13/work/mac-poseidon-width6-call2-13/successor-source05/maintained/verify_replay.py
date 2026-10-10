"""CLOSED portable DATA replay: regenerate45sources, never invoke a theorem prover."""
import argparse,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site,'use-I-B-S'
S=Path(__file__).resolve().parent
parser=argparse.ArgumentParser()
for name in ['inventory','source-inventory','input','parameters','topology','output-dir']:parser.add_argument('--'+name,type=Path,required=True)
parser.add_argument('--inventory-sha256',required=True)
parser.add_argument('--source-inventory-sha256',required=True)
args=parser.parse_args();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(args.inventory)==args.inventory_sha256 and sha(args.source_inventory)==args.source_inventory_sha256
inventory=json.loads(args.inventory.read_text());source_inventory=json.loads(args.source_inventory.read_text())
def closed():
    assert {p.name for p in S.iterdir()}==set(inventory['maintained_files']),'unlisted maintained entry'
    for name,e in inventory['maintained_files'].items():
        p=S/name;assert p.is_file() and not p.is_symlink() and sha(p)==e['sha256'] and p.stat().st_size==e['bytes'],'maintained identity mismatch: '+name
    assert sha(Path(__file__))==inventory['maintained_files'][Path(__file__).name]['sha256'],'executing recipe mismatch'
closed()
assert not args.output_dir.exists(),'fresh replay directory required'
args.output_dir.mkdir(parents=True)
assert sha(args.input)==source_inventory['input_sha256'] and sha(args.parameters)==source_inventory['parameters_sha256'] and sha(args.topology)==source_inventory['topology_sha256']
commands=[
 [sys.executable,'-I','-B','-S',str(S/'generate_probe.py'),'--input',str(args.input),'--parameters',str(args.parameters),'--output-dir',str(args.output_dir/'sources'),'--metadata-dir',str(args.output_dir/'probe-metadata')],
 [sys.executable,'-I','-B','-S',str(S/'generate_successors.py'),'--input',str(args.input),'--parameters',str(args.parameters),'--topology',str(args.topology),'--output-dir',str(args.output_dir/'sources'),'--metadata-dir',str(args.output_dir/'successor-metadata')]
]
observations=[]
for index,command in enumerate(commands):
    closed()
    proc=subprocess.run(command,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60)
    (args.output_dir/f'generator{index:02d}.stdout.txt').write_text(proc.stdout)
    (args.output_dir/f'generator{index:02d}.stderr.txt').write_text(proc.stderr)
    observations.append({'command':command,'exit':proc.returncode,'stdout_sha256':sha(args.output_dir/f'generator{index:02d}.stdout.txt'),'stderr_sha256':sha(args.output_dir/f'generator{index:02d}.stderr.txt')})
    closed()
    assert proc.returncode==0,'generator refusal; logs preserved'
expected={name+'.lean' for name in source_inventory['modules']}
assert {p.name for p in (args.output_dir/'sources').iterdir()}==expected
for name,entry in source_inventory['modules'].items():
    p=args.output_dir/'sources'/(name+'.lean')
    assert p.is_file() and not p.is_symlink() and sha(p)==entry['sha256'] and p.stat().st_size==entry['bytes'],'source byte mismatch: '+name
closed()
result={'status':'passed','schema':'call13-supported-replay01','sources':45,'source_bytes':sum(x['bytes'] for x in source_inventory['modules'].values()),
        'commands':observations,'executing_recipe_sha256':sha(Path(__file__)),'maintained_inventory_sha256':sha(args.inventory),'source_inventory_sha256':sha(args.source_inventory),
        'isolated_flags':['-I','-B','-S'],'Python_version':sys.version,'kernel_runs':0,'scope':'DATA byte regeneration only; two accepted source bytes unchanged,43successor sources remain unbuilt'}
with (args.output_dir/'replay-result01.json').open('x') as handle:json.dump(result,handle,indent=2);handle.write('\n')
print(json.dumps({'status':'passed','sources':45,'source_bytes':result['source_bytes'],'kernel_runs':0}))
