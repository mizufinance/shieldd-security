"""Selected-source Lean replay with finite physical budgets; histories stay local."""
from pathlib import Path
import argparse, hashlib, json, os, re, runpy, shutil, signal, subprocess, time
def require(x,m):
    if not x: raise ValueError(m)
def pin(p):
    p=Path(p);h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(65536),b''):h.update(b)
    return dict(path=str(p),bytes=p.stat().st_size,sha256=h.hexdigest())
def checked(r):
    require(pin(r['path'])==r,'selected file changed: '+r['path'])
def dump(p,o):p.write_text(json.dumps(o,sort_keys=True)+'\n')
def sha(data):return hashlib.sha256(data).hexdigest()
def parse_complete_audit(data, names):
    text=data.decode('utf-8'); remaining=text; records=[]
    require(not re.search(r'(?m)^(?:/[^\n]*:[0-9]+:[0-9]+: *| *)(?:warning|info|trace|error|panic)\s*:|sorryAx|uncaught exception|internal exception',text,re.I), 'diagnostic refusal')
    for name in names:
        pattern=r'^@?'+re.escape(name)+r'(?:\.\{[^}\n]*\})?\s*:[\s\S]*?^\''+re.escape(name)+r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$"
        matches=list(re.finditer(pattern,remaining,re.M))
        require(len(matches)==1, 'unique full-signature/axiom pair: '+name)
        m=matches[0]; axioms=[] if m.group(1) is None else [x.strip() for x in m.group(1).split(',') if x.strip()]
        require(set(axioms)<= {'propext','Quot.sound','Classical.choice'}, 'nonstandard axiom')
        full=m.group(0).split("\n'"+name+"'",1)[0].strip()
        records.append({'name':name,'full_type':full,'full_type_sha256':sha(full.encode()),'axioms':axioms})
        remaining=remaining[:m.start()]+remaining[m.end():]
    require(not remaining.strip(), 'unexplained/duplicate stdout')
    return records

def resources(root):
    raw=subprocess.check_output(['/usr/bin/memory_pressure','-Q'],text=True,timeout=10)
    disk=os.statvfs(root)
    return dict(free_memory_percent=int(re.search(r'System-wide memory free percentage:\s*(\d+)%',raw)[1]),free_disk_bytes=disk.f_bavail*disk.f_frsize)
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--root',default='ConcreteCofactorModel01');ap.add_argument('--extra-source',type=Path);ap.add_argument('--source-root',type=Path,action='append',default=[]);ap.add_argument('--reuse',type=Path,action='append',default=[]);a=ap.parse_args()
base=Path(__file__).resolve().parents[2];out=a.output.resolve();require(not out.exists(),'fresh output');out.mkdir(parents=True)
review=base/'work/resumed-orchestration-20261009-01/group-source-review-20261012'
c=json.loads((review/'current-config.json').read_bytes())
oldguard=base/'work/mac-bounded-target-heap295-source01/guard.py';require(pin(oldguard)['sha256']=='7406a9a37182ebf84bedb18bc5067863bf3aa1359b77762ded0adfbf9584b3fc','original pure parser')
g=runpy.run_path(str(oldguard),run_name='SOURCE_ONLY')
checked(c['closure']);available=json.loads(Path(c['closure']['path']).read_bytes())['modules'];available.update(c['qualified_batch_imports'])
# The most recent successful narrow batch is not yet in the inherited map.
batch=base/'work/mac-full-arithmetic45-execution328'
for line in (batch/'runtime/ledger.jsonl').read_text().splitlines():
    e=json.loads(line)
    if e['kind']!='result':continue
    checked(e['receipt']);r=json.loads(Path(e['receipt']['path']).read_bytes())
    if r['status']!='passed':continue
    name=r['module'];slots={suffix:next((v for p,v in r['objects'].items() if p.endswith('/'+name+suffix)),None) for suffix in g['SUFFIXES']}
    available[name]=dict(source=r['source'],receipt=e['receipt'],object=slots['.olean'],current_slots=slots)
for previous in a.reuse:
    progress=json.loads((previous.resolve()/'progress.json').read_bytes())
    for item in progress:
        if item['status']!='passed':continue
        checked(item['receipt']);r=json.loads(Path(item['receipt']['path']).read_bytes());require(r['status']=='passed','successful narrow predecessor')
        available[item['module']]=dict(source=r['source'],receipt=item['receipt'],object=r['objects']['.olean'],current_slots={suffix:r['objects'].get(suffix) for suffix in g['SUFFIXES']})
original=json.loads((base/'work/resumed-orchestration-20261009-01/group-metadata-review-20261012/packet/closure-manifest.json').read_bytes())['selected']
fresh={n:review/'packet/source/ShielddSecurity'/(n+'.lean') for n in original if n not in available}
for directory in a.source_root:
    for source in sorted((directory.resolve()/'ShielddSecurity').glob('*.lean')):
        if source.stem in available:
            identity=pin(source);prior=available[source.stem]['source']
            require(identity['bytes']==prior['bytes'] and identity['sha256']==prior['sha256'],'unchanged reused logical module: '+source.stem)
        else:fresh[source.stem]=source
if a.extra_source:fresh[a.root]=a.extra_source.resolve()
records={str(oldguard):pin(oldguard),str(Path(__file__)):pin(Path(__file__))}
selected={};order=[];visiting=set();official_needed=set()
def visit(n):
    if not n.startswith('ShielddSecurity.'):official_needed.add(n);return
    name=n.removeprefix('ShielddSecurity.')
    if name in selected:return
    require(name not in visiting,'acyclic imports');visiting.add(name)
    if name in fresh:
        src=fresh[name];identity=pin(src)
        if name in original:
            want=original[name]['source'];require(identity['bytes']==want['bytes'] and identity['sha256']==want['sha256'],'exact desktop source')
        row=dict(source=identity,replay=True)
    else:
        require(name in available,'missing selected dependency: '+name);row=dict(available[name]);row['replay']=False
        for r in [row['source'],row.get('receipt')]+list(row['current_slots'].values()):
            if r:checked(r);records[r['path']]=r
    data=Path(row['source']['path']).read_bytes();imports=g['uncached_direct_imports'](data)
    for child in imports:visit(child)
    row['imports']=imports
    row['heap_MiB']=1536
    if row['replay']:
        clean=g['strip_comments'](data.decode());audits=re.findall(r'(?m)^#check @([A-Za-z0-9_.]+)\s*$',clean)
        require(audits and audits==re.findall(r'(?m)^#print axioms ([A-Za-z0-9_.]+)\s*$',clean),'complete audit inventory: '+name)
        forbidden=r'\b(?:sorry|admit|axiom|unsafe|implemented_by|extern|native_decide|run_tac|elab|initialize|macro|IO|ofReduceBool|skipKernelTC)\b|decide\s*\+native|#(?:eval|reduce|run|compile)|\bimport\s+all\b'
        require(len(data)<=262144 and not re.search(forbidden,clean),'source feature check: '+name)
        quotation_check=re.sub(r'(?m)^local notation \"base\" => ConcretePointOperationPilot01\.base\s*$', '',clean)
        if name=='TransferReadback':
            require(identity['sha256']=='0af3de530ac872f31af6c05cff90ed17b212a760d6cc5f957b29b4841451220e','exact reviewed native domain literal source')
            for literal in ['def keyDomain : String := "shieldd.spend-nullifier.v1" ++ String.singleton (Char.ofNat 0)', 'def rootsDomain : String := "shieldd.nomt.roots.v1" ++ String.singleton (Char.ofNat 0)', 'def spentValue : String := "shieldd.spent.v1"']:
                require(quotation_check.count(literal)==1,'exact native domain literal definition')
                quotation_check=quotation_check.replace(literal,'')
        require('"' not in quotation_check and '`' not in quotation_check,'source quotation refusal: '+name)
        for key,val in re.findall(r'(?m)^\s*set_option\s+(\S+)\s+([^\n]+)',clean):
            val=val.strip()
            require((key=='maxHeartbeats' and val.isdecimal() and 0<int(val)<=900000) or (key=='maxRecDepth' and val.isdecimal() and 0<int(val)<=8192) or (key,val) in [('autoImplicit','false'),('pp.all','true in'),('linter.dupNamespace','false')],'finite options: '+name)
        require(set(re.findall(r'(?m)^\s*(#[A-Za-z_]+)',re.sub(r'(?m)^(\s*)#v(?=\[)',r'\1',clean)))<= {'#check','#print'},'source command whitelist')
        row['audits']=audits;order.append(name);records[row['source']['path']]=row['source']
    selected[name]=row;visiting.remove(name)
visit('ShielddSecurity.'+a.root)
project=base/'work/mac-poseidon-call1-plan14/successor-source02/project';toolchain=Path('/Users/antoinecyr/.elan/toolchains/leanprover--lean4---v4.30.0')
official_path=base/'work/mac-field-official273-data02/official-union01.json';require(pin(official_path)['sha256']=='f204fb1e606092bc9f3279524542e2d33b5f00d1cff54bfe094f1581229bc2d1','original official manifest');official=json.loads(official_path.read_bytes())
require(official['manifest']['revisions']['mathlib']=='c5ea00351c28e24afc9f0f84379aa41082b1188f','exact Mathlib')
packages=[project/'.lake/packages'/n for n in ['mathlib','plausible','LeanSearchClient','importGraph','proofwidgets','aesop','Qq','batteries','Cli']]
object_roots=[p/'.lake/build/lib/lean' for p in packages]+[toolchain/'lib/lean'];source_roots=packages+[toolchain/'src/lean'];official_visited=set()
official_cache_validated=False
def official_visit(name):
    global official_cache_validated
    if name in official_visited:return
    official_visited.add(name);relative=Path(name.replace('.','/'))
    sources=[r/relative.with_suffix('.lean') for r in source_roots if (r/relative.with_suffix('.lean')).is_file()]
    require(len(sources)==1,'one official source: '+name);records[str(sources[0])]=pin(sources[0])
    objects=[r/relative.with_suffix('.olean') for r in object_roots if (r/relative.with_suffix('.olean')).is_file()]
    require(len(objects)==1,'one official object: '+name)
    for suffix in g['SUFFIXES']:
        p=Path(str(objects[0].with_suffix(''))+suffix)
        if p.exists():
            r=official['slots'].get(str(p))
            if r is None and not official_cache_validated:
                cache_receipt=base/'work/mac-elliptic-official-cache334/receipt.json';cr=json.loads(cache_receipt.read_bytes());require(cr['exit']==0 and cr['stop'] is None,'bounded official cache receipt')
                require(subprocess.check_output(['git','-C',str(packages[0]),'rev-parse','HEAD'],text=True).strip()==official['manifest']['revisions']['mathlib'],'exact official checkout')
                require(not subprocess.check_output(['git','-C',str(packages[0]),'status','--porcelain','--untracked-files=no']),'clean official source')
                records[str(cache_receipt)]=pin(cache_receipt);official_cache_validated=True
            if r is None:r=pin(p)
            checked(r);records[str(p)]=r
    for child in g['official_header'](sources[0].read_bytes()):official_visit(child)
for n in sorted(official_needed):official_visit(n)
lean=toolchain/'bin/lean';checked(official['slots'][str(lean)]);records[str(lean)]=pin(lean)
for p,r in official['slots'].items():
    if Path(p).parent==toolchain/'lib/lean' and Path(p).suffix=='.dylib':checked(r);records[p]=r
links={}
cache=out/'objects';(cache/'ShielddSecurity').mkdir(parents=True)
for name,row in selected.items():
    if not row['replay']:
        for suffix,r in row['current_slots'].items():
            if r:
                dest=cache/'ShielddSecurity'/(name+suffix);target=Path(r['path']).resolve();dest.symlink_to(target);links[str(dest)]=str(target);require(pin(dest)['sha256']==r['sha256'],'linked immutable selected object');records[str(dest)]=pin(dest)
plan=dict(dependency_storage='one exact selected symlink per logical object; original identities and link targets checked before and after',selected_links=links,root=a.root,selected=selected,order=order,official_modules=sorted(official_visited),files=records,runtime_sha=c['runtime_sha'],mathlib=official['manifest']['revisions']['mathlib'],limits=dict(threads=1,default_heap_MiB=1536,elliptic_point_closure_heap_MiB=1536,rss_bytes=4*1024**3,module_seconds=240,heartbeats=900000,recDepth=8192,free_memory_percent=15,free_disk_bytes=2*1024**3),certification=False)
dump(out/'dependency-manifest.json',plan);print(json.dumps(dict(event='prepared',selected=len(selected),replay=len(order),official=len(official_visited))),flush=True)
for line in subprocess.check_output(['ps','-axo','comm='],text=True).splitlines():require(Path(line.strip()).name not in {'lean','lake','cargo','rustc','clang','clang++'},'one heavy verifier')
env=os.environ.copy();env.update(LEAN_NUM_THREADS='1',LEAN_PATH=':'.join(map(str,[cache]+object_roots)),TMPDIR=str(out))
completed=[]
def checked_links():
    for destination,target in links.items():
        require(Path(destination).is_symlink() and os.readlink(destination)==target,'unchanged selected link target: '+destination)
checked_links()
for ordinal,name in enumerate(order):
    row=selected[name];checked(row['source'])
    for child in row['imports']:
        if child.startswith('ShielddSecurity.'):
            childname=child.removeprefix('ShielddSecurity.');require((cache/'ShielddSecurity'/(childname+'.olean')).is_file(),'dependency object exists')
    floor=resources(out);require(floor['free_memory_percent']>=15 and floor['free_disk_bytes']>=2*1024**3,'physical admission')
    job=out/'runs'/name;job.mkdir(parents=True);src=Path(row['source']['path'])
    command=[str(lean),'-j1','-M'+str(row['heap_MiB']),'-DmaxHeartbeats=900000','-DmaxRecDepth=8192','-Dlinter.all=false','-R',str(src.parents[1]),'-o',str(cache/'ShielddSecurity'/(name+'.olean')),'-i',str(cache/'ShielddSecurity'/(name+'.ilean')),str(src)]
    begin=time.monotonic();peak=0;stop=None;samples=[]
    with (job/'stdout.txt').open('wb') as stdout,(job/'stderr.txt').open('wb') as stderr:
        child=subprocess.Popen(command,env=env,cwd=out,stdout=stdout,stderr=stderr,start_new_session=True)
        try:
            while child.poll() is None:
                ps=subprocess.check_output(['ps','-axo','pgid=,rss='],text=True,timeout=10).splitlines()
                rss=sum(int(r.split()[1])*1024 for r in ps if r.split() and int(r.split()[0])==child.pid);elapsed=time.monotonic()-begin;peak=max(peak,rss);sample=resources(out);samples.append(dict(seconds=elapsed,rss_bytes=rss,**sample))
                if rss>4*1024**3:stop='process-group resident limit'
                elif elapsed>240:stop='240 second limit'
                elif sample['free_memory_percent']<15 or sample['free_disk_bytes']<2*1024**3:stop='physical RAM/disk floor'
                if (job/'stdout.txt').stat().st_size>2*1024**2 or (job/'stderr.txt').stat().st_size>2*1024**2:stop='log byte limit'
                if stop:break
                time.sleep(.25)
        finally:
            if child.poll() is None:
                os.killpg(child.pid,signal.SIGTERM)
                try:child.wait(timeout=10)
                except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL);child.wait()
    code=child.wait();elapsed=time.monotonic()-begin;checked(row['source']);audits=[];audit_error=None
    if code==0 and not stop:
        try:
            require(not (job/'stderr.txt').read_bytes().strip(),'empty successful stderr');audit_bytes=(job/'stdout.txt').read_bytes()
            qualified=re.findall(r"(?m)^'([^']+)' (?:depends on axioms:|does not depend on any axioms)",audit_bytes.decode())
            require(len(qualified)==len(row['audits']) and all(q==n or q.endswith('.'+n) for q,n in zip(qualified,row['audits'])),'exact qualified audit resolution')
            require(len(set(qualified))==len(qualified),'unique qualified audit names')
            audits=parse_complete_audit(audit_bytes,qualified)
        except Exception as e:audit_error=str(e)
    objects={suffix:pin(cache/'ShielddSecurity'/(name+suffix)) for suffix in g['SUFFIXES'] if (cache/'ShielddSecurity'/(name+suffix)).exists()}
    result=dict(status='passed' if code==0 and not stop and not audit_error else 'incomplete',module=name,exit=code,stop=stop,audit_error=audit_error,seconds=elapsed,peak_group_rss_bytes=peak,command=command,source=row['source'],audits=audits,objects=objects,stdout=pin(job/'stdout.txt'),stderr=pin(job/'stderr.txt'),samples=samples,dependency_manifest=pin(out/'dependency-manifest.json'),certification=False,native_credit=0)
    dump(job/'receipt.json',result);completed.append(dict(module=name,status=result['status'],receipt=pin(job/'receipt.json')));dump(out/'progress.json',completed)
    print(json.dumps({k:result[k] for k in ['module','status','seconds','peak_group_rss_bytes','audit_error','stop']}),flush=True)
    if result['status']!='passed':break
    for r in objects.values():records[r['path']]=r
checked_links()
for r in records.values():checked(r)
dump(out/'completion.json',dict(root=a.root,status='passed' if len(completed)==len(order) and all(r['status']=='passed' for r in completed) else 'incomplete',completed=completed,dependency_manifest=pin(out/'dependency-manifest.json'),final_files=records,certification=False))

