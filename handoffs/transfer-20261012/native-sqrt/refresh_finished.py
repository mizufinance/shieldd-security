"""Generate and atomically publish the successful ff finished-phase audits."""
from pathlib import Path
import argparse, hashlib, importlib.util, json, os, shutil, tempfile

NAMES=['Inner','Inner.mk','Inner.k','Inner.b2k','Inner.z','Inner.below','State','State.mk',
       'State.x','State.b','State.z','State.v','InnerDone','Finished','innerStep','inner_done_step',
       'inner_done_fold','range_lower_bound','innerFor','inner_for_finished','outerStep',
       'outer_finished','outerLoop','finished_loop','finished_payload']

def digest(data):return hashlib.sha256(data).hexdigest()

def require(ok,message):
    if not ok:raise ValueError(message)

def pinned(r):
    data=Path(r['path']).read_bytes()
    require(len(data)==r['bytes'] and digest(data)==r['sha256'],'exact successful artifact')
    return data

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--receipt',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    root=Path(__file__).resolve().parent
    raw=args.receipt.read_bytes();r=json.loads(raw)
    require(r['status']=='passed' and r['exit']==0 and not r['stop'] and not r['audit_error'],'terminal success')
    require(r['command'][1:3]==['-j1','-M2048'] and r['seconds']<=240 and r['peak_group_rss_bytes']<=4*1024**3,'bounded compiler')
    names=['ShielddSecurity.FfFinishedPhase296.'+s for s in NAMES]
    body=(root/'source/ShielddSecurity/FfFinishedPhase296.lean').read_text()
    data=(body+'\n'+''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n' for n in names)).encode()
    require(data==pinned(r['source']),'maintained body reproduces successful source')
    require(not pinned(r['stderr']).strip(),'empty successful stderr')
    spec=importlib.util.spec_from_file_location('reports',root.parent/'native-packing/refresh.py')
    helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
    audits=helper.parse_reports(pinned(r['stdout']),names)
    require(audits==r['audits'],'complete independent type/axiom census')
    dependencies=json.loads(pinned(r['dependency_manifest']))
    require(all(not n.startswith('ShielddSecurity.') for n in dependencies['official_modules']),'official-library-only scope')
    for dep in dependencies['files'].values():pinned(dep)
    for obj in r['objects'].values():pinned(obj)
    pinned(r['guard'])
    require(r['samples'] and all(s['free_memory_percent']>=15 and s['free_disk_bytes']>=2*1024**3 for s in r['samples']),'physical/disk floors')
    require(not args.output.exists(),'fresh immutable output')
    staging=Path(tempfile.mkdtemp(prefix='.refresh-',dir=args.output.parent))
    try:
        p=staging/'source/ShielddSecurity/FfFinishedPhase296.lean';p.parent.mkdir(parents=True);p.write_bytes(data)
        evidence=dict(status='finished_phase_preservation_passed',certification=False,native_credit=0,full_transfer='OPEN',
                      scope='Exact mathematical ff inner/outer schedule preserves a reached root with v=1,b²=1,z²=1. Initial square completeness, active progress and native word-to-field correspondence remain open.',
                      audits=audits,source_sha256=digest(data),source_bytes=len(data),seconds=r['seconds'],
                      peak_group_rss_bytes=r['peak_group_rss_bytes'],command=r['command'],limits=r['limits'],
                      original_successful_receipt_sha256=digest(raw),original_stdout_sha256=r['stdout']['sha256'],
                      dependency_manifest_sha256=r['dependency_manifest']['sha256'],official_modules=len(dependencies['official_modules']),
                      guard_sha256=r['guard']['sha256'],object_identities={k:{a:v[a] for a in ['bytes','sha256']} for k,v in r['objects'].items()})
        (staging/'evidence.json').write_text(json.dumps(evidence,indent=2)+'\n')
        os.replace(staging,args.output)
        print(json.dumps(dict(audits=len(audits),certification=False,native_credit=0)))
    finally:
        if staging.exists():shutil.rmtree(staging)

if __name__=='__main__':main()
