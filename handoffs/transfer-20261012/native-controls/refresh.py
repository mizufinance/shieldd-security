"""Verify a successful local diagnostic replay; publish compact evidence only."""
from pathlib import Path
import argparse, hashlib, importlib.util, json, os, subprocess, tempfile

def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for data in iter(lambda:f.read(65536),b''):h.update(data)
    return h.hexdigest()

def require(ok,message):
    if not ok:raise ValueError(message)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--run',type=Path,required=True)
    parser.add_argument('--packet',type=Path,required=True)
    parser.add_argument('--runtime',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    shape=json.loads((args.packet/'native3/native3-shape.json').read_bytes())
    git=lambda *a:subprocess.check_output(['git','-C',str(args.runtime),*a],text=True).strip()
    require(git('rev-parse','HEAD')==shape['runtime_sha'] and not git('status','--porcelain'), 'clean exact runtime')
    require(not args.output.exists(),'fresh evidence destination')
    inv_path=args.run/'source-inventory.json'
    inv=json.loads(inv_path.read_bytes())
    require(inv['runtime_sha']==shape['runtime_sha'] and inv['diagnostic_only'] and not inv['certification'],'diagnostic inventory scope')
    for r in inv['files']:
        relative=Path(r['path'])
        require(not relative.is_absolute() and '..' not in relative.parts,'ordinary relative source')
        p=args.run/'source'/relative
        require(p.is_file() and p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],'source inventory identity')
    for r in shape['overlay']:
        p=args.run/'source'/r['path']
        require(p.stat().st_size==r['after']['bytes'] and sha(p)==r['after']['sha256'],'exact diagnostic overlay')
    builds=[]
    for folder in ['build01','setup-build01']:
        p=args.run/folder/'receipt.json';r=json.loads(p.read_bytes())
        require(r['status']=='build_passed' and r['exit']==0 and not r['stop'],'successful finite build')
        require(r['source_inventory_sha256']==sha(inv_path),'same build sources')
        require(len(r['binaries'])==1 and sha(Path(r['binaries'][0]['path']))==r['binaries'][0]['sha256'],'exact built binary')
        builds.append(dict(original_receipt_sha256=sha(p),command=r['command'],seconds=r['seconds'],
                           peak_group_rss_bytes=r['peak_group_rss_bytes'],binaries=r['binaries']))
    setup_path=args.run/'registry-setup01/receipt.json'
    setup=json.loads(setup_path.read_bytes())
    require(setup['status']=='setup_passed' and setup['exit']==0 and not setup['stop'],'successful fresh setup')
    key_files={p.name:dict(bytes=p.stat().st_size,sha256=sha(p)) for p in sorted((args.run/'registry01').iterdir()) if p.is_file()}
    require(key_files==setup['registry'] and len(key_files)==15,'exact complete fresh registry')
    manifest=json.loads((args.run/'registry01/manifest.json').read_bytes())
    transfer=[e for e in manifest['entries'] if e['family']=='transfer']
    require(len(transfer)==1 and transfer[0]['relation']==shape['transfer_relation'] and
            transfer[0]['domain_size']==shape['transfer_domain'],'exact Transfer relation and domain')
    out=args.run/'native-tests01';r=json.loads((out/'receipt.json').read_bytes())
    require(r['status']=='three_native_controls_passed' and r['exit']==0 and not r['stop'],'terminal semantic success')
    require(r['test_names']==shape['test_names'] and r['registry']==key_files,'exact tests and registry')
    require(r['source_inventory_sha256']==sha(inv_path) and r['binary']==builds[0]['binaries'][0],'exact test build association')
    spec=importlib.util.spec_from_file_location('complete_native_group',args.packet/'native3/review-only-windows-recipe/group-result.py')
    group=importlib.util.module_from_spec(spec);spec.loader.exec_module(group)
    stdout=(out/'stdout.txt').read_text()
    group.parse((out/'libtest-results.txt').read_bytes(),stdout,shape['test_names'])
    text=stdout+'\n'+(out/'stderr.txt').read_text()
    for marker in shape['expected_observations']:require(text.count(marker)==1,'unique intended semantic observation')
    require(r['observations']==shape['expected_observations'],'complete observation census')
    for folder in ['build01','setup-build01','registry-setup01','native-tests01']:
        result=json.loads((args.run/folder/'receipt.json').read_bytes())
        samples=json.loads((args.run/folder/'samples.json').read_bytes())
        require(result['seconds']<7200 and result['peak_group_rss_bytes']<=4*1024**3,'time/RSS bounds')
        require(samples and all(s['free_memory_percent']>=15 and s['free_disk_bytes']>=2*1024**3 for s in samples),'physical/disk floors')
    evidence=dict(status='three_named_native_diagnostic_controls_passed',runtime_sha=shape['runtime_sha'],
                  full_transfer='OPEN',certification=False,native_controls=3,test_names=r['test_names'],observations=r['observations'],
                  seconds=r['seconds'],peak_group_rss_bytes=r['peak_group_rss_bytes'],limits=r['limits'],builds=builds,
                  registry_scope=r['registry_scope'],registry_files=key_files,transfer_registry_entry=transfer[0],
                  setup=dict(seconds=setup['seconds'],peak_group_rss_bytes=setup['peak_group_rss_bytes'],original_receipt_sha256=sha(setup_path)),
                  source_inventory_sha256=sha(inv_path),source_files=len(inv['files']),diagnostic_overlay=shape['overlay'],
                  original_test_receipt_sha256=sha(out/'receipt.json'),original_stdout_sha256=sha(out/'stdout.txt'),
                  original_stderr_sha256=sha(out/'stderr.txt'),original_libtest_results_sha256=sha(out/'libtest-results.txt'),
                  scope='Actual native diagnostic tests over an exact 52-path test/observer overlay of the pinned runtime. Private duplicate-queue injection is artificial. Passing tests do not establish whole native trace refinement, universal retry safety, natural IO-failure reachability or Transfer certification. Original diagnostic sources and logs remain local.')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    fd,name=tempfile.mkstemp(prefix='.evidence-',dir=args.output.parent)
    try:
        with os.fdopen(fd,'w') as f:f.write(json.dumps(evidence,indent=2)+'\n')
        os.replace(name,args.output)
    finally:
        if Path(name).exists():Path(name).unlink()
    print(json.dumps(dict(native_controls=3,certification=False,full_transfer='OPEN')))

if __name__=='__main__':main()
